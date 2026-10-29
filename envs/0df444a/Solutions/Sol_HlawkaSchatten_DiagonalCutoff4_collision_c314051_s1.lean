-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314051_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:10.577486+00:00
-- url     : https://prove2.me/submissions/bde5092a-7f52-4b6a-8706-564a1ac40ab1

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
theorem collision_support_c314051_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1831582473/5000000000 : ℝ)*x 0 + (1827119277/5000000000 : ℝ)*x 1 + (5233514599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1831582473/5000000000 : ℝ)^19 ≤ (28025381585753/100000000000000 : ℝ)^15 := by
    have hnat : (1831582473 : ℕ)^19*100000000000000^15 ≤ 28025381585753^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831582473 5000000000 28025381585753 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1827119277/5000000000 : ℝ)^19 ≤ (1396945313619/5000000000000 : ℝ)^15 := by
    have hnat : (1827119277 : ℕ)^19*5000000000000^15 ≤ 1396945313619^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827119277 5000000000 1396945313619 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233514599/10000000000 : ℝ)^19 ≤ (44035712128017/100000000000000 : ℝ)^15 := by
    have hnat : (5233514599 : ℕ)^19*100000000000000^15 ≤ 44035712128017^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233514599 10000000000 44035712128017 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1831582473/5000000000 : ℝ), (1827119277/5000000000 : ℝ), (5233514599/10000000000 : ℝ)] ![(28025381585753/100000000000000 : ℝ), (1396945313619/5000000000000 : ℝ), (44035712128017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1831582473/5000000000 : ℝ)|^19 ≤ (28025381585753/100000000000000 : ℝ)^15
        have hw : |(-1831582473/5000000000 : ℝ)|=(1831582473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1827119277/5000000000 : ℝ)|^19 ≤ (1396945313619/5000000000000 : ℝ)^15
        have hw : |(1827119277/5000000000 : ℝ)|=(1827119277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233514599/10000000000 : ℝ)|^19 ≤ (44035712128017/100000000000000 : ℝ)^15
        have hw : |(5233514599/10000000000 : ℝ)|=(5233514599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (35790357/125000000 : ℝ)*x 0 + (-714062863/2500000000 : ℝ)*x 1 + (103071053/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35790357/125000000 : ℝ)^19 ≤ (10256227044407/50000000000000 : ℝ)^15 := by
    have hnat : (35790357 : ℕ)^19*50000000000000^15 ≤ 10256227044407^15*125000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35790357 125000000 10256227044407 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (714062863/2500000000 : ℝ)^19 ≤ (5112290181159/25000000000000 : ℝ)^15 := by
    have hnat : (714062863 : ℕ)^19*25000000000000^15 ≤ 5112290181159^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714062863 2500000000 5112290181159 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103071053/156250000 : ℝ)^19 ≤ (5903838517361/10000000000000 : ℝ)^15 := by
    have hnat : (103071053 : ℕ)^19*10000000000000^15 ≤ 5903838517361^15*156250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103071053 156250000 5903838517361 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35790357/125000000 : ℝ), (-714062863/2500000000 : ℝ), (103071053/156250000 : ℝ)] ![(10256227044407/50000000000000 : ℝ), (5112290181159/25000000000000 : ℝ), (5903838517361/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35790357/125000000 : ℝ)|^19 ≤ (10256227044407/50000000000000 : ℝ)^15
        have hw : |(35790357/125000000 : ℝ)|=(35790357/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-714062863/2500000000 : ℝ)|^19 ≤ (5112290181159/25000000000000 : ℝ)^15
        have hw : |(-714062863/2500000000 : ℝ)|=(714062863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103071053/156250000 : ℝ)|^19 ≤ (5903838517361/10000000000000 : ℝ)^15
        have hw : |(103071053/156250000 : ℝ)|=(103071053/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5412402743/10000000000 : ℝ)*x 0 + (1355966069/2500000000 : ℝ)*x 1 + (-13581269/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412402743/10000000000 : ℝ)^19 ≤ (1148772795319/2500000000000 : ℝ)^15 := by
    have hnat : (5412402743 : ℕ)^19*2500000000000^15 ≤ 1148772795319^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412402743 10000000000 1148772795319 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355966069/2500000000 : ℝ)^19 ≤ (46074202882997/100000000000000 : ℝ)^15 := by
    have hnat : (1355966069 : ℕ)^19*100000000000000^15 ≤ 46074202882997^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355966069 2500000000 46074202882997 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13581269/100000000 : ℝ)^19 ≤ (7974885289573/100000000000000 : ℝ)^15 := by
    have hnat : (13581269 : ℕ)^19*100000000000000^15 ≤ 7974885289573^15*100000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13581269 100000000 7974885289573 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412402743/10000000000 : ℝ), (1355966069/2500000000 : ℝ), (-13581269/100000000 : ℝ)] ![(1148772795319/2500000000000 : ℝ), (46074202882997/100000000000000 : ℝ), (7974885289573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412402743/10000000000 : ℝ)|^19 ≤ (1148772795319/2500000000000 : ℝ)^15
        have hw : |(5412402743/10000000000 : ℝ)|=(5412402743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355966069/2500000000 : ℝ)|^19 ≤ (46074202882997/100000000000000 : ℝ)^15
        have hw : |(1355966069/2500000000 : ℝ)|=(1355966069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13581269/100000000 : ℝ)|^19 ≤ (7974885289573/100000000000000 : ℝ)^15
        have hw : |(-13581269/100000000 : ℝ)|=(13581269/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (128620549/250000000 : ℝ)*x 0 + (1288929213/2500000000 : ℝ)*x 1 + (1040912693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128620549/250000000 : ℝ)^19 ≤ (43092574757967/100000000000000 : ℝ)^15 := by
    have hnat : (128620549 : ℕ)^19*100000000000000^15 ≤ 43092574757967^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128620549 250000000 43092574757967 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288929213/2500000000 : ℝ)^19 ≤ (21604098303203/50000000000000 : ℝ)^15 := by
    have hnat : (1288929213 : ℕ)^19*50000000000000^15 ≤ 21604098303203^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288929213 2500000000 21604098303203 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040912693/5000000000 : ℝ)^19 ≤ (13699228618321/100000000000000 : ℝ)^15 := by
    have hnat : (1040912693 : ℕ)^19*100000000000000^15 ≤ 13699228618321^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040912693 5000000000 13699228618321 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128620549/250000000 : ℝ), (1288929213/2500000000 : ℝ), (1040912693/5000000000 : ℝ)] ![(43092574757967/100000000000000 : ℝ), (21604098303203/50000000000000 : ℝ), (13699228618321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128620549/250000000 : ℝ)|^19 ≤ (43092574757967/100000000000000 : ℝ)^15
        have hw : |(128620549/250000000 : ℝ)|=(128620549/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1288929213/2500000000 : ℝ)|^19 ≤ (21604098303203/50000000000000 : ℝ)^15
        have hw : |(1288929213/2500000000 : ℝ)|=(1288929213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040912693/5000000000 : ℝ)|^19 ≤ (13699228618321/100000000000000 : ℝ)^15
        have hw : |(1040912693/5000000000 : ℝ)|=(1040912693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-138550339/400000000 : ℝ)*x 0 + (3093306461/10000000000 : ℝ)*x 1 + (5901309937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138550339/400000000 : ℝ)^19 ≤ (26107199935421/100000000000000 : ℝ)^15 := by
    have hnat : (138550339 : ℕ)^19*100000000000000^15 ≤ 26107199935421^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138550339 400000000 26107199935421 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3093306461/10000000000 : ℝ)^19 ≤ (5655561686267/25000000000000 : ℝ)^15 := by
    have hnat : (3093306461 : ℕ)^19*25000000000000^15 ≤ 5655561686267^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093306461 10000000000 5655561686267 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5901309937/10000000000 : ℝ)^19 ≤ (25635276648059/50000000000000 : ℝ)^15 := by
    have hnat : (5901309937 : ℕ)^19*50000000000000^15 ≤ 25635276648059^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5901309937 10000000000 25635276648059 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138550339/400000000 : ℝ), (3093306461/10000000000 : ℝ), (5901309937/10000000000 : ℝ)] ![(26107199935421/100000000000000 : ℝ), (5655561686267/25000000000000 : ℝ), (25635276648059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138550339/400000000 : ℝ)|^19 ≤ (26107199935421/100000000000000 : ℝ)^15
        have hw : |(-138550339/400000000 : ℝ)|=(138550339/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3093306461/10000000000 : ℝ)|^19 ≤ (5655561686267/25000000000000 : ℝ)^15
        have hw : |(3093306461/10000000000 : ℝ)|=(3093306461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5901309937/10000000000 : ℝ)|^19 ≤ (25635276648059/50000000000000 : ℝ)^15
        have hw : |(5901309937/10000000000 : ℝ)|=(5901309937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2721466423/10000000000 : ℝ)*x 0 + (-2430403197/10000000000 : ℝ)*x 1 + (3519495641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2721466423/10000000000 : ℝ)^19 ≤ (4808656820609/25000000000000 : ℝ)^15 := by
    have hnat : (2721466423 : ℕ)^19*25000000000000^15 ≤ 4808656820609^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721466423 10000000000 4808656820609 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2430403197/10000000000 : ℝ)^19 ≤ (16667068303563/100000000000000 : ℝ)^15 := by
    have hnat : (2430403197 : ℕ)^19*100000000000000^15 ≤ 16667068303563^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2430403197 10000000000 16667068303563 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3519495641/5000000000 : ℝ)^19 ≤ (2563932176239/4000000000000 : ℝ)^15 := by
    have hnat : (3519495641 : ℕ)^19*4000000000000^15 ≤ 2563932176239^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3519495641 5000000000 2563932176239 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2721466423/10000000000 : ℝ), (-2430403197/10000000000 : ℝ), (3519495641/5000000000 : ℝ)] ![(4808656820609/25000000000000 : ℝ), (16667068303563/100000000000000 : ℝ), (2563932176239/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2721466423/10000000000 : ℝ)|^19 ≤ (4808656820609/25000000000000 : ℝ)^15
        have hw : |(2721466423/10000000000 : ℝ)|=(2721466423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2430403197/10000000000 : ℝ)|^19 ≤ (16667068303563/100000000000000 : ℝ)^15
        have hw : |(-2430403197/10000000000 : ℝ)|=(2430403197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3519495641/5000000000 : ℝ)|^19 ≤ (2563932176239/4000000000000 : ℝ)^15
        have hw : |(3519495641/5000000000 : ℝ)|=(3519495641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5117781151/10000000000 : ℝ)*x 0 + (1528847801/2500000000 : ℝ)*x 1 + (-717886131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5117781151/10000000000 : ℝ)^19 ≤ (42805886921187/100000000000000 : ℝ)^15 := by
    have hnat : (5117781151 : ℕ)^19*100000000000000^15 ≤ 42805886921187^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117781151 10000000000 42805886921187 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1528847801/2500000000 : ℝ)^19 ≤ (6704721183641/12500000000000 : ℝ)^15 := by
    have hnat : (1528847801 : ℕ)^19*12500000000000^15 ≤ 6704721183641^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528847801 2500000000 6704721183641 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (717886131/10000000000 : ℝ)^19 ≤ (355634359351/10000000000000 : ℝ)^15 := by
    have hnat : (717886131 : ℕ)^19*10000000000000^15 ≤ 355634359351^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717886131 10000000000 355634359351 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5117781151/10000000000 : ℝ), (1528847801/2500000000 : ℝ), (-717886131/10000000000 : ℝ)] ![(42805886921187/100000000000000 : ℝ), (6704721183641/12500000000000 : ℝ), (355634359351/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5117781151/10000000000 : ℝ)|^19 ≤ (42805886921187/100000000000000 : ℝ)^15
        have hw : |(5117781151/10000000000 : ℝ)|=(5117781151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1528847801/2500000000 : ℝ)|^19 ≤ (6704721183641/12500000000000 : ℝ)^15
        have hw : |(1528847801/2500000000 : ℝ)|=(1528847801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-717886131/10000000000 : ℝ)|^19 ≤ (355634359351/10000000000000 : ℝ)^15
        have hw : |(-717886131/10000000000 : ℝ)|=(717886131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_12 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5019815593/10000000000 : ℝ)*x 0 + (5998329201/10000000000 : ℝ)*x 1 + (534488351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5019815593/10000000000 : ℝ)^19 ≤ (8354128718347/20000000000000 : ℝ)^15 := by
    have hnat : (5019815593 : ℕ)^19*20000000000000^15 ≤ 8354128718347^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019815593 10000000000 8354128718347 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5998329201/10000000000 : ℝ)^19 ≤ (52340561371971/100000000000000 : ℝ)^15 := by
    have hnat : (5998329201 : ℕ)^19*100000000000000^15 ≤ 52340561371971^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998329201 10000000000 52340561371971 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534488351/5000000000 : ℝ)^19 ≤ (588879501847/10000000000000 : ℝ)^15 := by
    have hnat : (534488351 : ℕ)^19*10000000000000^15 ≤ 588879501847^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534488351 5000000000 588879501847 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5019815593/10000000000 : ℝ), (5998329201/10000000000 : ℝ), (534488351/5000000000 : ℝ)] ![(8354128718347/20000000000000 : ℝ), (52340561371971/100000000000000 : ℝ), (588879501847/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5019815593/10000000000 : ℝ)|^19 ≤ (8354128718347/20000000000000 : ℝ)^15
        have hw : |(5019815593/10000000000 : ℝ)|=(5019815593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5998329201/10000000000 : ℝ)|^19 ≤ (52340561371971/100000000000000 : ℝ)^15
        have hw : |(5998329201/10000000000 : ℝ)|=(5998329201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(534488351/5000000000 : ℝ)|^19 ≤ (588879501847/10000000000000 : ℝ)^15
        have hw : |(534488351/5000000000 : ℝ)|=(534488351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1551078631/5000000000 : ℝ)*x 0 + (1727575831/5000000000 : ℝ)*x 1 + (368832569/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1551078631/5000000000 : ℝ)^19 ≤ (4540853480347/20000000000000 : ℝ)^15 := by
    have hnat : (1551078631 : ℕ)^19*20000000000000^15 ≤ 4540853480347^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551078631 5000000000 4540853480347 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1727575831/5000000000 : ℝ)^19 ≤ (203320753103/781250000000 : ℝ)^15 := by
    have hnat : (1727575831 : ℕ)^19*781250000000^15 ≤ 203320753103^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727575831 5000000000 203320753103 781250000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368832569/625000000 : ℝ)^19 ≤ (10254135237337/20000000000000 : ℝ)^15 := by
    have hnat : (368832569 : ℕ)^19*20000000000000^15 ≤ 10254135237337^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368832569 625000000 10254135237337 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1551078631/5000000000 : ℝ), (1727575831/5000000000 : ℝ), (368832569/625000000 : ℝ)] ![(4540853480347/20000000000000 : ℝ), (203320753103/781250000000 : ℝ), (10254135237337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1551078631/5000000000 : ℝ)|^19 ≤ (4540853480347/20000000000000 : ℝ)^15
        have hw : |(-1551078631/5000000000 : ℝ)|=(1551078631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1727575831/5000000000 : ℝ)|^19 ≤ (203320753103/781250000000 : ℝ)^15
        have hw : |(1727575831/5000000000 : ℝ)|=(1727575831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(368832569/625000000 : ℝ)|^19 ≤ (10254135237337/20000000000000 : ℝ)^15
        have hw : |(368832569/625000000 : ℝ)|=(368832569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (609339357/2500000000 : ℝ)*x 0 + (-271470427/1000000000 : ℝ)*x 1 + (7038998841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (609339357/2500000000 : ℝ)^19 ≤ (16727499039569/100000000000000 : ℝ)^15 := by
    have hnat : (609339357 : ℕ)^19*100000000000000^15 ≤ 16727499039569^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609339357 2500000000 16727499039569 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271470427/1000000000 : ℝ)^19 ≤ (9587054671203/50000000000000 : ℝ)^15 := by
    have hnat : (271470427 : ℕ)^19*50000000000000^15 ≤ 9587054671203^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271470427 1000000000 9587054671203 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7038998841/10000000000 : ℝ)^19 ≤ (64098391595209/100000000000000 : ℝ)^15 := by
    have hnat : (7038998841 : ℕ)^19*100000000000000^15 ≤ 64098391595209^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7038998841 10000000000 64098391595209 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(609339357/2500000000 : ℝ), (-271470427/1000000000 : ℝ), (7038998841/10000000000 : ℝ)] ![(16727499039569/100000000000000 : ℝ), (9587054671203/50000000000000 : ℝ), (64098391595209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(609339357/2500000000 : ℝ)|^19 ≤ (16727499039569/100000000000000 : ℝ)^15
        have hw : |(609339357/2500000000 : ℝ)|=(609339357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-271470427/1000000000 : ℝ)|^19 ≤ (9587054671203/50000000000000 : ℝ)^15
        have hw : |(-271470427/1000000000 : ℝ)|=(271470427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7038998841/10000000000 : ℝ)|^19 ≤ (64098391595209/100000000000000 : ℝ)^15
        have hw : |(7038998841/10000000000 : ℝ)|=(7038998841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6104117869/10000000000 : ℝ)*x 0 + (5129604143/10000000000 : ℝ)*x 1 + (-358936383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6104117869/10000000000 : ℝ)^19 ≤ (2140502201199/4000000000000 : ℝ)^15 := by
    have hnat : (6104117869 : ℕ)^19*4000000000000^15 ≤ 2140502201199^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6104117869 10000000000 2140502201199 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129604143/10000000000 : ℝ)^19 ≤ (1073279630713/2500000000000 : ℝ)^15 := by
    have hnat : (5129604143 : ℕ)^19*2500000000000^15 ≤ 1073279630713^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129604143 10000000000 1073279630713 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (358936383/5000000000 : ℝ)^19 ≤ (3556259728969/100000000000000 : ℝ)^15 := by
    have hnat : (358936383 : ℕ)^19*100000000000000^15 ≤ 3556259728969^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358936383 5000000000 3556259728969 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6104117869/10000000000 : ℝ), (5129604143/10000000000 : ℝ), (-358936383/5000000000 : ℝ)] ![(2140502201199/4000000000000 : ℝ), (1073279630713/2500000000000 : ℝ), (3556259728969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6104117869/10000000000 : ℝ)|^19 ≤ (2140502201199/4000000000000 : ℝ)^15
        have hw : |(6104117869/10000000000 : ℝ)|=(6104117869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129604143/10000000000 : ℝ)|^19 ≤ (1073279630713/2500000000000 : ℝ)^15
        have hw : |(5129604143/10000000000 : ℝ)|=(5129604143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-358936383/5000000000 : ℝ)|^19 ≤ (3556259728969/100000000000000 : ℝ)^15
        have hw : |(-358936383/5000000000 : ℝ)|=(358936383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_18 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5987274673/10000000000 : ℝ)*x 0 + (5031414797/10000000000 : ℝ)*x 1 + (33404887/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5987274673/10000000000 : ℝ)^19 ≤ (13054602113409/25000000000000 : ℝ)^15 := by
    have hnat : (5987274673 : ℕ)^19*25000000000000^15 ≤ 13054602113409^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5987274673 10000000000 13054602113409 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5031414797/10000000000 : ℝ)^19 ≤ (1047323457309/2500000000000 : ℝ)^15 := by
    have hnat : (5031414797 : ℕ)^19*2500000000000^15 ≤ 1047323457309^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031414797 10000000000 1047323457309 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33404887/312500000 : ℝ)^19 ≤ (5888653243229/100000000000000 : ℝ)^15 := by
    have hnat : (33404887 : ℕ)^19*100000000000000^15 ≤ 5888653243229^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33404887 312500000 5888653243229 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5987274673/10000000000 : ℝ), (5031414797/10000000000 : ℝ), (33404887/312500000 : ℝ)] ![(13054602113409/25000000000000 : ℝ), (1047323457309/2500000000000 : ℝ), (5888653243229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5987274673/10000000000 : ℝ)|^19 ≤ (13054602113409/25000000000000 : ℝ)^15
        have hw : |(5987274673/10000000000 : ℝ)|=(5987274673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5031414797/10000000000 : ℝ)|^19 ≤ (1047323457309/2500000000000 : ℝ)^15
        have hw : |(5031414797/10000000000 : ℝ)|=(5031414797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33404887/312500000 : ℝ)|^19 ≤ (5888653243229/100000000000000 : ℝ)^15
        have hw : |(33404887/312500000 : ℝ)|=(33404887/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_19 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3776366513/10000000000 : ℝ)*x 0 + (7535459/20000000 : ℝ)*x 1 + (1256375861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3776366513/10000000000 : ℝ)^19 ≤ (14563438034999/50000000000000 : ℝ)^15 := by
    have hnat : (3776366513 : ℕ)^19*50000000000000^15 ≤ 14563438034999^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3776366513 10000000000 14563438034999 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7535459/20000000 : ℝ)^19 ≤ (7260630154687/25000000000000 : ℝ)^15 := by
    have hnat : (7535459 : ℕ)^19*25000000000000^15 ≤ 7260630154687^15*20000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7535459 20000000 7260630154687 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1256375861/2500000000 : ℝ)^19 ≤ (41830603304729/100000000000000 : ℝ)^15 := by
    have hnat : (1256375861 : ℕ)^19*100000000000000^15 ≤ 41830603304729^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256375861 2500000000 41830603304729 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3776366513/10000000000 : ℝ), (7535459/20000000 : ℝ), (1256375861/2500000000 : ℝ)] ![(14563438034999/50000000000000 : ℝ), (7260630154687/25000000000000 : ℝ), (41830603304729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3776366513/10000000000 : ℝ)|^19 ≤ (14563438034999/50000000000000 : ℝ)^15
        have hw : |(-3776366513/10000000000 : ℝ)|=(3776366513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7535459/20000000 : ℝ)|^19 ≤ (7260630154687/25000000000000 : ℝ)^15
        have hw : |(7535459/20000000 : ℝ)|=(7535459/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1256375861/2500000000 : ℝ)|^19 ≤ (41830603304729/100000000000000 : ℝ)^15
        have hw : |(1256375861/2500000000 : ℝ)|=(1256375861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1388654001/5000000000 : ℝ)*x 0 + (-2769973773/10000000000 : ℝ)*x 1 + (6733407631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1388654001/5000000000 : ℝ)^19 ≤ (2466988569523/12500000000000 : ℝ)^15 := by
    have hnat : (1388654001 : ℕ)^19*12500000000000^15 ≤ 2466988569523^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388654001 5000000000 2466988569523 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2769973773/10000000000 : ℝ)^19 ≤ (19669915712217/100000000000000 : ℝ)^15 := by
    have hnat : (2769973773 : ℕ)^19*100000000000000^15 ≤ 19669915712217^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769973773 10000000000 19669915712217 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6733407631/10000000000 : ℝ)^19 ≤ (946783995579/1562500000000 : ℝ)^15 := by
    have hnat : (6733407631 : ℕ)^19*1562500000000^15 ≤ 946783995579^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6733407631 10000000000 946783995579 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1388654001/5000000000 : ℝ), (-2769973773/10000000000 : ℝ), (6733407631/10000000000 : ℝ)] ![(2466988569523/12500000000000 : ℝ), (19669915712217/100000000000000 : ℝ), (946783995579/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1388654001/5000000000 : ℝ)|^19 ≤ (2466988569523/12500000000000 : ℝ)^15
        have hw : |(1388654001/5000000000 : ℝ)|=(1388654001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2769973773/10000000000 : ℝ)|^19 ≤ (19669915712217/100000000000000 : ℝ)^15
        have hw : |(-2769973773/10000000000 : ℝ)|=(2769973773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6733407631/10000000000 : ℝ)|^19 ≤ (946783995579/1562500000000 : ℝ)^15
        have hw : |(6733407631/10000000000 : ℝ)|=(6733407631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (733832969/1250000000 : ℝ)*x 0 + (974270363/2000000000 : ℝ)*x 1 + (-737532573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (733832969/1250000000 : ℝ)^19 ≤ (10186706431509/20000000000000 : ℝ)^15 := by
    have hnat : (733832969 : ℕ)^19*20000000000000^15 ≤ 10186706431509^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733832969 1250000000 10186706431509 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974270363/2000000000 : ℝ)^19 ≤ (502650410139/1250000000000 : ℝ)^15 := by
    have hnat : (974270363 : ℕ)^19*1250000000000^15 ≤ 502650410139^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974270363 2000000000 502650410139 1250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (737532573/5000000000 : ℝ)^19 ≤ (2213608754083/25000000000000 : ℝ)^15 := by
    have hnat : (737532573 : ℕ)^19*25000000000000^15 ≤ 2213608754083^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737532573 5000000000 2213608754083 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(733832969/1250000000 : ℝ), (974270363/2000000000 : ℝ), (-737532573/5000000000 : ℝ)] ![(10186706431509/20000000000000 : ℝ), (502650410139/1250000000000 : ℝ), (2213608754083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(733832969/1250000000 : ℝ)|^19 ≤ (10186706431509/20000000000000 : ℝ)^15
        have hw : |(733832969/1250000000 : ℝ)|=(733832969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(974270363/2000000000 : ℝ)|^19 ≤ (502650410139/1250000000000 : ℝ)^15
        have hw : |(974270363/2000000000 : ℝ)|=(974270363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-737532573/5000000000 : ℝ)|^19 ≤ (2213608754083/25000000000000 : ℝ)^15
        have hw : |(-737532573/5000000000 : ℝ)|=(737532573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314051_s1_s1_25 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4081269443/10000000000 : ℝ)*x 0 + (819995079/1250000000 : ℝ)*x 1 + (1525405787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4081269443/10000000000 : ℝ)^19 ≤ (16068574226297/50000000000000 : ℝ)^15 := by
    have hnat : (4081269443 : ℕ)^19*50000000000000^15 ≤ 16068574226297^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4081269443 10000000000 16068574226297 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (819995079/1250000000 : ℝ)^19 ≤ (2931196271479/5000000000000 : ℝ)^15 := by
    have hnat : (819995079 : ℕ)^19*5000000000000^15 ≤ 2931196271479^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819995079 1250000000 2931196271479 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1525405787/10000000000 : ℝ)^19 ≤ (1847785221121/20000000000000 : ℝ)^15 := by
    have hnat : (1525405787 : ℕ)^19*20000000000000^15 ≤ 1847785221121^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525405787 10000000000 1847785221121 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4081269443/10000000000 : ℝ), (819995079/1250000000 : ℝ), (1525405787/10000000000 : ℝ)] ![(16068574226297/50000000000000 : ℝ), (2931196271479/5000000000000 : ℝ), (1847785221121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4081269443/10000000000 : ℝ)|^19 ≤ (16068574226297/50000000000000 : ℝ)^15
        have hw : |(4081269443/10000000000 : ℝ)|=(4081269443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(819995079/1250000000 : ℝ)|^19 ≤ (2931196271479/5000000000000 : ℝ)^15
        have hw : |(819995079/1250000000 : ℝ)|=(819995079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1525405787/10000000000 : ℝ)|^19 ≤ (1847785221121/20000000000000 : ℝ)^15
        have hw : |(1525405787/10000000000 : ℝ)|=(1525405787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314051_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((9501/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9501/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3763/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3763/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18351/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18351/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((36337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2267/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2267/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6161/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(6161/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (9501/12500 : ℝ) ^ (37/8 : ℝ) ≤ (2811734346483601941/10000000000000000000 : ℝ) := by
    have hpowers : (9501/12500 : ℝ)^37 ≤ (2811734346483601941/10000000000000000000 : ℝ)^8 := by
      have hnat : (9501 : ℕ)^37*10000000000000000000^8 ≤ 2811734346483601941^8*12500^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9501 12500 2811734346483601941 10000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9501/12500 : ℝ)) (X := (2811734346483601941/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (12811734346483601941/10000000000000000000 : ℝ) ≤ (10550342981521139/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (12811734346483601941/10000000000000000000 : ℝ)^8 ≤ (10550342981521139/10000000000000000 : ℝ)^37 := by
      have hnat : (12811734346483601941 : ℕ)^8*10000000000000000^37 ≤ 10550342981521139^37*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12811734346483601941 10000000000000000000 10550342981521139 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10550342981521139/10000000000000000 : ℝ)) (X := (12811734346483601941/10000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (7811734346483601941/5000000000000000000 : ℝ) ≤ (11012801960186979/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (7811734346483601941/5000000000000000000 : ℝ)^8 ≤ (11012801960186979/10000000000000000 : ℝ)^37 := by
      have hnat : (7811734346483601941 : ℕ)^8*10000000000000000^37 ≤ 11012801960186979^37*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7811734346483601941 5000000000000000000 11012801960186979 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11012801960186979/10000000000000000 : ℝ)) (X := (7811734346483601941/5000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(550342981521139/7600800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5780737233323/95010000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (9501/12500 : ℝ)) (alpha := (550342981521139/7600800000000000 : ℝ)) (beta := (5780737233323/95010000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9501/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(550342981521139/7600800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5780737233323/95010000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3763/5000 : ℝ) ^ (37/8 : ℝ) ≤ (671505382824363761/2500000000000000000 : ℝ) := by
    have hpowers : (3763/5000 : ℝ)^37 ≤ (671505382824363761/2500000000000000000 : ℝ)^8 := by
      have hnat : (3763 : ℕ)^37*2500000000000000000^8 ≤ 671505382824363761^8*5000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3763 5000 671505382824363761 2500000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3763/5000 : ℝ)) (X := (671505382824363761/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3171505382824363761/2500000000000000000 : ℝ) ≤ (10527872982133483/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3171505382824363761/2500000000000000000 : ℝ)^8 ≤ (10527872982133483/10000000000000000 : ℝ)^37 := by
      have hnat : (3171505382824363761 : ℕ)^8*10000000000000000^37 ≤ 10527872982133483^37*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3171505382824363761 2500000000000000000 10527872982133483 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10527872982133483/10000000000000000 : ℝ)) (X := (3171505382824363761/2500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1921505382824363761/1250000000000000000 : ℝ) ≤ (10974238601016761/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (1921505382824363761/1250000000000000000 : ℝ)^8 ≤ (10974238601016761/10000000000000000 : ℝ)^37 := by
      have hnat : (1921505382824363761 : ℕ)^8*10000000000000000^37 ≤ 10974238601016761^37*1250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1921505382824363761 1250000000000000000 10974238601016761 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10974238601016761/10000000000000000 : ℝ)) (X := (1921505382824363761/1250000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(527872982133483/7526000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(223182809441639/3763000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (3763/5000 : ℝ)) (alpha := (527872982133483/7526000000000000 : ℝ)) (beta := (223182809441639/3763000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (3763/5000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(527872982133483/7526000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(223182809441639/3763000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (18351/50000 : ℝ) ^ (37/8 : ℝ) ≤ (484908737486140443/50000000000000000000 : ℝ) := by
    have hpowers : (18351/50000 : ℝ)^37 ≤ (484908737486140443/50000000000000000000 : ℝ)^8 := by
      have hnat : (18351 : ℕ)^37*50000000000000000000^8 ≤ 484908737486140443^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18351 50000 484908737486140443 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18351/50000 : ℝ)) (X := (484908737486140443/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50484908737486140443/50000000000000000000 : ℝ) ≤ (5010444893666087/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (50484908737486140443/50000000000000000000 : ℝ)^8 ≤ (5010444893666087/5000000000000000 : ℝ)^37 := by
      have hnat : (50484908737486140443 : ℕ)^8*5000000000000000^37 ≤ 5010444893666087^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50484908737486140443 50000000000000000000 5010444893666087 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010444893666087/5000000000000000 : ℝ)) (X := (50484908737486140443/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25484908737486140443/25000000000000000000 : ℝ) ≤ (39225089445377/39062500000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (25484908737486140443/25000000000000000000 : ℝ)^8 ≤ (39225089445377/39062500000000 : ℝ)^37 := by
      have hnat : (25484908737486140443 : ℕ)^8*39062500000000^37 ≤ 39225089445377^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25484908737486140443 25000000000000000000 39225089445377 39062500000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39225089445377/39062500000000 : ℝ)) (X := (25484908737486140443/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(3481631222029/611700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(10366555342169/1835100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (18351/50000 : ℝ)) (alpha := (3481631222029/611700000000000 : ℝ)) (beta := (10366555342169/1835100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (18351/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(3481631222029/611700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(10366555342169/1835100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1831582473/5000000000 : ℝ)*X 0 0+(1827119277/5000000000 : ℝ)*X 0 1+(5233514599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((35790357/125000000 : ℝ)*X 1 0+(-714062863/2500000000 : ℝ)*X 1 1+(103071053/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5412402743/10000000000 : ℝ)*X 2 0+(1355966069/2500000000 : ℝ)*X 2 1+(-13581269/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((128620549/250000000 : ℝ)*X 0 0+(1288929213/2500000000 : ℝ)*X 0 1+(1040912693/5000000000 : ℝ)*X 0 2+(128620549/250000000 : ℝ)*X 1 0+(1288929213/2500000000 : ℝ)*X 1 1+(1040912693/5000000000 : ℝ)*X 1 2+(128620549/250000000 : ℝ)*X 2 0+(1288929213/2500000000 : ℝ)*X 2 1+(1040912693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-138550339/400000000 : ℝ)*X 0 0+(3093306461/10000000000 : ℝ)*X 0 1+(5901309937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2721466423/10000000000 : ℝ)*X 1 0+(-2430403197/10000000000 : ℝ)*X 1 1+(3519495641/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5117781151/10000000000 : ℝ)*X 2 0+(1528847801/2500000000 : ℝ)*X 2 1+(-717886131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((5019815593/10000000000 : ℝ)*X 0 0+(5998329201/10000000000 : ℝ)*X 0 1+(534488351/5000000000 : ℝ)*X 0 2+(5019815593/10000000000 : ℝ)*X 1 0+(5998329201/10000000000 : ℝ)*X 1 1+(534488351/5000000000 : ℝ)*X 1 2+(5019815593/10000000000 : ℝ)*X 2 0+(5998329201/10000000000 : ℝ)*X 2 1+(534488351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-1551078631/5000000000 : ℝ)*X 0 0+(1727575831/5000000000 : ℝ)*X 0 1+(368832569/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((609339357/2500000000 : ℝ)*X 1 0+(-271470427/1000000000 : ℝ)*X 1 1+(7038998841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6104117869/10000000000 : ℝ)*X 2 0+(5129604143/10000000000 : ℝ)*X 2 1+(-358936383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((5987274673/10000000000 : ℝ)*X 0 0+(5031414797/10000000000 : ℝ)*X 0 1+(33404887/312500000 : ℝ)*X 0 2+(5987274673/10000000000 : ℝ)*X 1 0+(5031414797/10000000000 : ℝ)*X 1 1+(33404887/312500000 : ℝ)*X 1 2+(5987274673/10000000000 : ℝ)*X 2 0+(5031414797/10000000000 : ℝ)*X 2 1+(33404887/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-3776366513/10000000000 : ℝ)*X 0 0+(7535459/20000000 : ℝ)*X 0 1+(1256375861/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1388654001/5000000000 : ℝ)*X 1 0+(-2769973773/10000000000 : ℝ)*X 1 1+(6733407631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((733832969/1250000000 : ℝ)*X 2 0+(974270363/2000000000 : ℝ)*X 2 1+(-737532573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((4081269443/10000000000 : ℝ)*X 0 0+(819995079/1250000000 : ℝ)*X 0 1+(1525405787/10000000000 : ℝ)*X 0 2+(4081269443/10000000000 : ℝ)*X 1 0+(819995079/1250000000 : ℝ)*X 1 1+(1525405787/10000000000 : ℝ)*X 1 2+(4081269443/10000000000 : ℝ)*X 2 0+(819995079/1250000000 : ℝ)*X 2 1+(1525405787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314051_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((36337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (94212764659262765532254083399/12149810709500000000000000000000000 : ℝ) := by norm_num
    linear_combination (303933/500000000000 : ℝ)*(base39) + (143412142367/500000000000 : ℝ)*(base49) + (4996770493/15625000000 : ℝ)*(base59) + (1836163011469/1000000000000 : ℝ)*(base60) + (1737691658103/250000000000 : ℝ)*(major_s1_0) + (1737691658103/250000000000 : ℝ)*(major_s1_1) + (1737691658103/250000000000 : ℝ)*(major_s1_2) + (7837397/500000000000 : ℝ)*(sp_s1_2) + (9862007795403/1000000000000 : ℝ)*(sp_s1_7) + (4930948502751/500000000000 : ℝ)*(sp_s1_8) + (9861992120609/1000000000000 : ℝ)*(sp_s1_9) + (504935802347/125000000000 : ℝ)*(sp_s1_12) + (110789901/1000000000000 : ℝ)*(sp_s1_14) + (1139559/31250000000 : ℝ)*(sp_s1_25) + (504940360583/125000000000 : ℝ)*(f.failure) + (9862007795403/1000000000000 : ℝ)*(f.sum) + (570906594572722279/3836378500000000000000000000000 : ℝ)*base62 + (253268007768437/305850000000000000000000000 : ℝ)*base64 + (40058784598379/470375000000000000000000000 : ℝ)*base67 + (13484846030807/25487500000000000000000000 : ℝ)*base68 + (1839551126462903893/3874507800000000000000000000000 : ℝ)*base70 + (680021134221/31670000000000000000000000 : ℝ)*base73 + (883005035919201/1881500000000000000000000000 : ℝ)*base74 + (286321363724041/633400000000000000000000000 : ℝ)*base76 + (661200630355563059/744838812500000000000000000000 : ℝ)*base79 + (6227/12500000000000000 : ℝ)*base87 + (6227/12500000000000000 : ℝ)*base89 + (6227/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2267/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2267/6250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (75213750814190749917737399181/4859924283800000000000000000000000 : ℝ) := by norm_num
    linear_combination (286782555609/1000000000000 : ℝ)*(base49) + (901436233921/1000000000000 : ℝ)*(base59) + (2088581421143/1000000000000 : ℝ)*(base60) + (6949669026033/1000000000000 : ℝ)*(major_s1_0) + (6949669026033/1000000000000 : ℝ)*(major_s1_1) + (6949669026033/1000000000000 : ℝ)*(major_s1_2) + (101922573/1000000000000 : ℝ)*(sp_s1_0) + (3575281/100000000000 : ℝ)*(sp_s1_6) + (1567033/12500000000 : ℝ)*(sp_s1_7) + (246505515269/25000000000 : ℝ)*(sp_s1_13) + (2465111973993/250000000000 : ℝ)*(sp_s1_14) + (4930142798457/500000000000 : ℝ)*(sp_s1_15) + (4038849244507/1000000000000 : ℝ)*(sp_s1_18) + (81149529/500000000000 : ℝ)*(sp_s1_21) + (4038884997317/1000000000000 : ℝ)*(f.failure) + (2465111973993/250000000000 : ℝ)*(f.sum) + (376812466203188481/15345514000000000000000000000000 : ℝ)*base63 + (27444634351563/203900000000000000000000000 : ℝ)*base65 + (646838857903413/3763000000000000000000000000 : ℝ)*base67 + (33065465157151/203900000000000000000000000 : ℝ)*base69 + (55252365638747521/5166010400000000000000000000000 : ℝ)*base70 + (15187669003953/31670000000000000000000000 : ℝ)*base73 + (2177122218411139/7526000000000000000000000000 : ℝ)*base75 + (723761383505969/2533600000000000000000000000 : ℝ)*base77 + (2507883189947994771/11917421000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (38873/100000000000000000 : ℝ)*base87 + (38873/100000000000000000 : ℝ)*base89 + (38873/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6161/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(6161/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2152297071648683955737523290633/145797728514000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1156947/1000000000000 : ℝ)*(base39) + (55889942089/125000000000 : ℝ)*(base49) + (328763954337/1000000000000 : ℝ)*(base60) + (3659853969839/1000000000000 : ℝ)*(major_s1_0) + (3659853969839/1000000000000 : ℝ)*(major_s1_1) + (3659853969839/1000000000000 : ℝ)*(major_s1_2) + (386179317/1000000000000 : ℝ)*(sp_s1_1) + (485483/100000000000 : ℝ)*(sp_s1_12) + (615827/125000000000 : ℝ)*(sp_s1_14) + (6484423/62500000000 : ℝ)*(sp_s1_15) + (162272943881/31250000000 : ℝ)*(sp_s1_19) + (5192343098259/1000000000000 : ℝ)*(sp_s1_20) + (324539403339/62500000000 : ℝ)*(sp_s1_21) + (2126963959913/1000000000000 : ℝ)*(sp_s1_25) + (2126968814743/1000000000000 : ℝ)*(f.failure) + (162272943881/31250000000 : ℝ)*(f.sum) + (16633911027908910931/46036542000000000000000000000000 : ℝ)*base62 + (1398180001898669/1835100000000000000000000000 : ℝ)*base64 + (957403013121821/3763000000000000000000000000 : ℝ)*base66 + (429190509435281/611700000000000000000000000 : ℝ)*base68 + (19728721641729066167/46494093600000000000000000000000 : ℝ)*base70 + (35327965729943/95010000000000000000000000 : ℝ)*base72 + (4510024876242163/7526000000000000000000000000 : ℝ)*base74 + (4980277138451779/7600800000000000000000000000 : ℝ)*base76 + (6745486469211821779/35752263000000000000000000000000 : ℝ)*base79 + (113267/100000000000000000 : ℝ)*base87 + (113267/100000000000000000 : ℝ)*base89 + (113267/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((9501/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9501/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3763/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3763/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18351/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18351/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((36337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2267/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2267/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6161/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(6161/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314051_s1 p hpa hpb X hX hprev0

#print axioms solution

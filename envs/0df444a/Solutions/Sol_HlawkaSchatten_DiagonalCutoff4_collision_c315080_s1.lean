-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315080_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:57:29.711624+00:00
-- url     : https://prove2.me/submissions/e90c7b19-c9ab-4d7a-aee2-856be37ed592

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
theorem collision_support_c315080_s1_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3342306409/10000000000 : ℝ)*x 0 + (5485425307/10000000000 : ℝ)*x 1 + (738485489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3342306409/10000000000 : ℝ)^19 ≤ (623828588531/2500000000000 : ℝ)^15 := by
    have hnat : (3342306409 : ℕ)^19*2500000000000^15 ≤ 623828588531^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3342306409 10000000000 623828588531 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485425307/10000000000 : ℝ)^19 ≤ (46737597844853/100000000000000 : ℝ)^15 := by
    have hnat : (5485425307 : ℕ)^19*100000000000000^15 ≤ 46737597844853^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485425307 10000000000 46737597844853 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738485489/2000000000 : ℝ)^19 ≤ (5661851721319/20000000000000 : ℝ)^15 := by
    have hnat : (738485489 : ℕ)^19*20000000000000^15 ≤ 5661851721319^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738485489 2000000000 5661851721319 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3342306409/10000000000 : ℝ), (5485425307/10000000000 : ℝ), (738485489/2000000000 : ℝ)] ![(623828588531/2500000000000 : ℝ), (46737597844853/100000000000000 : ℝ), (5661851721319/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3342306409/10000000000 : ℝ)|^19 ≤ (623828588531/2500000000000 : ℝ)^15
        have hw : |(-3342306409/10000000000 : ℝ)|=(3342306409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485425307/10000000000 : ℝ)|^19 ≤ (46737597844853/100000000000000 : ℝ)^15
        have hw : |(5485425307/10000000000 : ℝ)|=(5485425307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(738485489/2000000000 : ℝ)|^19 ≤ (5661851721319/20000000000000 : ℝ)^15
        have hw : |(738485489/2000000000 : ℝ)|=(738485489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (237219939/400000000 : ℝ)*x 0 + (-556526623/10000000000 : ℝ)*x 1 + (1080268501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (237219939/400000000 : ℝ)^19 ≤ (6448997340781/12500000000000 : ℝ)^15 := by
    have hnat : (237219939 : ℕ)^19*12500000000000^15 ≤ 6448997340781^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237219939 400000000 6448997340781 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (556526623/10000000000 : ℝ)^19 ≤ (2576017822867/100000000000000 : ℝ)^15 := by
    have hnat : (556526623 : ℕ)^19*100000000000000^15 ≤ 2576017822867^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556526623 10000000000 2576017822867 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080268501/2000000000 : ℝ)^19 ≤ (22916001719923/50000000000000 : ℝ)^15 := by
    have hnat : (1080268501 : ℕ)^19*50000000000000^15 ≤ 22916001719923^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080268501 2000000000 22916001719923 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(237219939/400000000 : ℝ), (-556526623/10000000000 : ℝ), (1080268501/2000000000 : ℝ)] ![(6448997340781/12500000000000 : ℝ), (2576017822867/100000000000000 : ℝ), (22916001719923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(237219939/400000000 : ℝ)|^19 ≤ (6448997340781/12500000000000 : ℝ)^15
        have hw : |(237219939/400000000 : ℝ)|=(237219939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-556526623/10000000000 : ℝ)|^19 ≤ (2576017822867/100000000000000 : ℝ)^15
        have hw : |(-556526623/10000000000 : ℝ)|=(556526623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080268501/2000000000 : ℝ)|^19 ≤ (22916001719923/50000000000000 : ℝ)^15
        have hw : |(1080268501/2000000000 : ℝ)|=(1080268501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (48115803/156250000 : ℝ)*x 0 + (745795061/1250000000 : ℝ)*x 1 + (-42524913/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48115803/156250000 : ℝ)^19 ≤ (2249360694411/10000000000000 : ℝ)^15 := by
    have hnat : (48115803 : ℕ)^19*10000000000000^15 ≤ 2249360694411^15*156250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48115803 156250000 2249360694411 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (745795061/1250000000 : ℝ)^19 ≤ (12996867634179/25000000000000 : ℝ)^15 := by
    have hnat : (745795061 : ℕ)^19*25000000000000^15 ≤ 12996867634179^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745795061 1250000000 12996867634179 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42524913/125000000 : ℝ)^19 ≤ (6379730625071/25000000000000 : ℝ)^15 := by
    have hnat : (42524913 : ℕ)^19*25000000000000^15 ≤ 6379730625071^15*125000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42524913 125000000 6379730625071 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48115803/156250000 : ℝ), (745795061/1250000000 : ℝ), (-42524913/125000000 : ℝ)] ![(2249360694411/10000000000000 : ℝ), (12996867634179/25000000000000 : ℝ), (6379730625071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48115803/156250000 : ℝ)|^19 ≤ (2249360694411/10000000000000 : ℝ)^15
        have hw : |(48115803/156250000 : ℝ)|=(48115803/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(745795061/1250000000 : ℝ)|^19 ≤ (12996867634179/25000000000000 : ℝ)^15
        have hw : |(745795061/1250000000 : ℝ)|=(745795061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42524913/125000000 : ℝ)|^19 ≤ (6379730625071/25000000000000 : ℝ)^15
        have hw : |(-42524913/125000000 : ℝ)|=(42524913/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (503174773/1250000000 : ℝ)*x 0 + (488588351/1000000000 : ℝ)*x 1 + (1833113557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503174773/1250000000 : ℝ)^19 ≤ (6316180526673/20000000000000 : ℝ)^15 := by
    have hnat : (503174773 : ℕ)^19*20000000000000^15 ≤ 6316180526673^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503174773 1250000000 6316180526673 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488588351/1000000000 : ℝ)^19 ≤ (10091009439933/25000000000000 : ℝ)^15 := by
    have hnat : (488588351 : ℕ)^19*25000000000000^15 ≤ 10091009439933^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488588351 1000000000 10091009439933 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833113557/5000000000 : ℝ)^19 ≤ (14027529798961/50000000000000 : ℝ)^15 := by
    have hnat : (1833113557 : ℕ)^19*50000000000000^15 ≤ 14027529798961^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833113557 5000000000 14027529798961 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(503174773/1250000000 : ℝ), (488588351/1000000000 : ℝ), (1833113557/5000000000 : ℝ)] ![(6316180526673/20000000000000 : ℝ), (10091009439933/25000000000000 : ℝ), (14027529798961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(503174773/1250000000 : ℝ)|^19 ≤ (6316180526673/20000000000000 : ℝ)^15
        have hw : |(503174773/1250000000 : ℝ)|=(503174773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(488588351/1000000000 : ℝ)|^19 ≤ (10091009439933/25000000000000 : ℝ)^15
        have hw : |(488588351/1000000000 : ℝ)|=(488588351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1833113557/5000000000 : ℝ)|^19 ≤ (14027529798961/50000000000000 : ℝ)^15
        have hw : |(1833113557/5000000000 : ℝ)|=(1833113557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3375638643/10000000000 : ℝ)*x 0 + (5499131781/10000000000 : ℝ)*x 1 + (911151449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3375638643/10000000000 : ℝ)^19 ≤ (3158596982807/12500000000000 : ℝ)^15 := by
    have hnat : (3375638643 : ℕ)^19*12500000000000^15 ≤ 3158596982807^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3375638643 10000000000 3158596982807 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499131781/10000000000 : ℝ)^19 ≤ (46885572980817/100000000000000 : ℝ)^15 := by
    have hnat : (5499131781 : ℕ)^19*100000000000000^15 ≤ 46885572980817^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499131781 10000000000 46885572980817 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (911151449/2500000000 : ℝ)^19 ≤ (6961412785757/25000000000000 : ℝ)^15 := by
    have hnat : (911151449 : ℕ)^19*25000000000000^15 ≤ 6961412785757^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911151449 2500000000 6961412785757 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3375638643/10000000000 : ℝ), (5499131781/10000000000 : ℝ), (911151449/2500000000 : ℝ)] ![(3158596982807/12500000000000 : ℝ), (46885572980817/100000000000000 : ℝ), (6961412785757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3375638643/10000000000 : ℝ)|^19 ≤ (3158596982807/12500000000000 : ℝ)^15
        have hw : |(-3375638643/10000000000 : ℝ)|=(3375638643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499131781/10000000000 : ℝ)|^19 ≤ (46885572980817/100000000000000 : ℝ)^15
        have hw : |(5499131781/10000000000 : ℝ)|=(5499131781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(911151449/2500000000 : ℝ)|^19 ≤ (6961412785757/25000000000000 : ℝ)^15
        have hw : |(911151449/2500000000 : ℝ)|=(911151449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (721205807/1250000000 : ℝ)*x 0 + (-6221849/1250000000 : ℝ)*x 1 + (5790393719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (721205807/1250000000 : ℝ)^19 ≤ (4982595778737/10000000000000 : ℝ)^15 := by
    have hnat : (721205807 : ℕ)^19*10000000000000^15 ≤ 4982595778737^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721205807 1250000000 4982595778737 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6221849/1250000000 : ℝ)^19 ≤ (121025989353/100000000000000 : ℝ)^15 := by
    have hnat : (6221849 : ℕ)^19*100000000000000^15 ≤ 121025989353^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6221849 1250000000 121025989353 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5790393719/10000000000 : ℝ)^19 ≤ (12513254050513/25000000000000 : ℝ)^15 := by
    have hnat : (5790393719 : ℕ)^19*25000000000000^15 ≤ 12513254050513^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5790393719 10000000000 12513254050513 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(721205807/1250000000 : ℝ), (-6221849/1250000000 : ℝ), (5790393719/10000000000 : ℝ)] ![(4982595778737/10000000000000 : ℝ), (121025989353/100000000000000 : ℝ), (12513254050513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(721205807/1250000000 : ℝ)|^19 ≤ (4982595778737/10000000000000 : ℝ)^15
        have hw : |(721205807/1250000000 : ℝ)|=(721205807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6221849/1250000000 : ℝ)|^19 ≤ (121025989353/100000000000000 : ℝ)^15
        have hw : |(-6221849/1250000000 : ℝ)|=(6221849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5790393719/10000000000 : ℝ)|^19 ≤ (12513254050513/25000000000000 : ℝ)^15
        have hw : |(5790393719/10000000000 : ℝ)|=(5790393719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1404744831/5000000000 : ℝ)*x 0 + (1624107863/2500000000 : ℝ)*x 1 + (-303334669/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1404744831/5000000000 : ℝ)^19 ≤ (5006506264753/25000000000000 : ℝ)^15 := by
    have hnat : (1404744831 : ℕ)^19*25000000000000^15 ≤ 5006506264753^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404744831 5000000000 5006506264753 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1624107863/2500000000 : ℝ)^19 ≤ (28952861579949/50000000000000 : ℝ)^15 := by
    have hnat : (1624107863 : ℕ)^19*50000000000000^15 ≤ 28952861579949^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624107863 2500000000 28952861579949 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (303334669/1000000000 : ℝ)^19 ≤ (4413650352541/20000000000000 : ℝ)^15 := by
    have hnat : (303334669 : ℕ)^19*20000000000000^15 ≤ 4413650352541^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303334669 1000000000 4413650352541 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1404744831/5000000000 : ℝ), (1624107863/2500000000 : ℝ), (-303334669/1000000000 : ℝ)] ![(5006506264753/25000000000000 : ℝ), (28952861579949/50000000000000 : ℝ), (4413650352541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1404744831/5000000000 : ℝ)|^19 ≤ (5006506264753/25000000000000 : ℝ)^15
        have hw : |(1404744831/5000000000 : ℝ)|=(1404744831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1624107863/2500000000 : ℝ)|^19 ≤ (28952861579949/50000000000000 : ℝ)^15
        have hw : |(1624107863/2500000000 : ℝ)|=(1624107863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-303334669/1000000000 : ℝ)|^19 ≤ (4413650352541/20000000000000 : ℝ)^15
        have hw : |(-303334669/1000000000 : ℝ)|=(303334669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_12 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (766437839/2000000000 : ℝ)*x 0 + (4900603913/10000000000 : ℝ)*x 1 + (961492373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (766437839/2000000000 : ℝ)^19 ≤ (2967331907721/10000000000000 : ℝ)^15 := by
    have hnat : (766437839 : ℕ)^19*10000000000000^15 ≤ 2967331907721^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766437839 2000000000 2967331907721 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4900603913/10000000000 : ℝ)^19 ≤ (40518139603699/100000000000000 : ℝ)^15 := by
    have hnat : (4900603913 : ℕ)^19*100000000000000^15 ≤ 40518139603699^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4900603913 10000000000 40518139603699 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961492373/2500000000 : ℝ)^19 ≤ (7452135327097/25000000000000 : ℝ)^15 := by
    have hnat : (961492373 : ℕ)^19*25000000000000^15 ≤ 7452135327097^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961492373 2500000000 7452135327097 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(766437839/2000000000 : ℝ), (4900603913/10000000000 : ℝ), (961492373/2500000000 : ℝ)] ![(2967331907721/10000000000000 : ℝ), (40518139603699/100000000000000 : ℝ), (7452135327097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(766437839/2000000000 : ℝ)|^19 ≤ (2967331907721/10000000000000 : ℝ)^15
        have hw : |(766437839/2000000000 : ℝ)|=(766437839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4900603913/10000000000 : ℝ)|^19 ≤ (40518139603699/100000000000000 : ℝ)^15
        have hw : |(4900603913/10000000000 : ℝ)|=(4900603913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961492373/2500000000 : ℝ)|^19 ≤ (7452135327097/25000000000000 : ℝ)^15
        have hw : |(961492373/2500000000 : ℝ)|=(961492373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3602168887/10000000000 : ℝ)*x 0 + (5482355939/10000000000 : ℝ)*x 1 + (3437832113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3602168887/10000000000 : ℝ)^19 ≤ (2743560172171/10000000000000 : ℝ)^15 := by
    have hnat : (3602168887 : ℕ)^19*10000000000000^15 ≤ 2743560172171^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3602168887 10000000000 2743560172171 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482355939/10000000000 : ℝ)^19 ≤ (46704474439637/100000000000000 : ℝ)^15 := by
    have hnat : (5482355939 : ℕ)^19*100000000000000^15 ≤ 46704474439637^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482355939 10000000000 46704474439637 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3437832113/10000000000 : ℝ)^19 ≤ (12929961908359/50000000000000 : ℝ)^15 := by
    have hnat : (3437832113 : ℕ)^19*50000000000000^15 ≤ 12929961908359^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3437832113 10000000000 12929961908359 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3602168887/10000000000 : ℝ), (5482355939/10000000000 : ℝ), (3437832113/10000000000 : ℝ)] ![(2743560172171/10000000000000 : ℝ), (46704474439637/100000000000000 : ℝ), (12929961908359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3602168887/10000000000 : ℝ)|^19 ≤ (2743560172171/10000000000000 : ℝ)^15
        have hw : |(-3602168887/10000000000 : ℝ)|=(3602168887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482355939/10000000000 : ℝ)|^19 ≤ (46704474439637/100000000000000 : ℝ)^15
        have hw : |(5482355939/10000000000 : ℝ)|=(5482355939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3437832113/10000000000 : ℝ)|^19 ≤ (12929961908359/50000000000000 : ℝ)^15
        have hw : |(3437832113/10000000000 : ℝ)|=(3437832113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (181236719/312500000 : ℝ)*x 0 + (-53125291/1000000000 : ℝ)*x 1 + (5548345191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181236719/312500000 : ℝ)^19 ≤ (2507678285263/5000000000000 : ℝ)^15 := by
    have hnat : (181236719 : ℕ)^19*5000000000000^15 ≤ 2507678285263^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181236719 312500000 2507678285263 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53125291/1000000000 : ℝ)^19 ≤ (607185907397/25000000000000 : ℝ)^15 := by
    have hnat : (53125291 : ℕ)^19*25000000000000^15 ≤ 607185907397^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53125291 1000000000 607185907397 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5548345191/10000000000 : ℝ)^19 ≤ (9483538130431/20000000000000 : ℝ)^15 := by
    have hnat : (5548345191 : ℕ)^19*20000000000000^15 ≤ 9483538130431^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5548345191 10000000000 9483538130431 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(181236719/312500000 : ℝ), (-53125291/1000000000 : ℝ), (5548345191/10000000000 : ℝ)] ![(2507678285263/5000000000000 : ℝ), (607185907397/25000000000000 : ℝ), (9483538130431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(181236719/312500000 : ℝ)|^19 ≤ (2507678285263/5000000000000 : ℝ)^15
        have hw : |(181236719/312500000 : ℝ)|=(181236719/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53125291/1000000000 : ℝ)|^19 ≤ (607185907397/25000000000000 : ℝ)^15
        have hw : |(-53125291/1000000000 : ℝ)|=(53125291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5548345191/10000000000 : ℝ)|^19 ≤ (9483538130431/20000000000000 : ℝ)^15
        have hw : |(5548345191/10000000000 : ℝ)|=(5548345191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2842508147/10000000000 : ℝ)*x 0 + (594065477/1000000000 : ℝ)*x 1 + (-3657600899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2842508147/10000000000 : ℝ)^19 ≤ (127028799457/625000000000 : ℝ)^15 := by
    have hnat : (2842508147 : ℕ)^19*625000000000^15 ≤ 127028799457^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842508147 10000000000 127028799457 625000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594065477/1000000000 : ℝ)^19 ≤ (51703919356897/100000000000000 : ℝ)^15 := by
    have hnat : (594065477 : ℕ)^19*100000000000000^15 ≤ 51703919356897^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594065477 1000000000 51703919356897 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3657600899/10000000000 : ℝ)^19 ≤ (2797147271983/10000000000000 : ℝ)^15 := by
    have hnat : (3657600899 : ℕ)^19*10000000000000^15 ≤ 2797147271983^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3657600899 10000000000 2797147271983 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2842508147/10000000000 : ℝ), (594065477/1000000000 : ℝ), (-3657600899/10000000000 : ℝ)] ![(127028799457/625000000000 : ℝ), (51703919356897/100000000000000 : ℝ), (2797147271983/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2842508147/10000000000 : ℝ)|^19 ≤ (127028799457/625000000000 : ℝ)^15
        have hw : |(2842508147/10000000000 : ℝ)|=(2842508147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(594065477/1000000000 : ℝ)|^19 ≤ (51703919356897/100000000000000 : ℝ)^15
        have hw : |(594065477/1000000000 : ℝ)|=(594065477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3657600899/10000000000 : ℝ)|^19 ≤ (2797147271983/10000000000000 : ℝ)^15
        have hw : |(-3657600899/10000000000 : ℝ)|=(3657600899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_19 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4404673311/10000000000 : ℝ)*x 0 + (2378597337/5000000000 : ℝ)*x 1 + (1704293639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4404673311/10000000000 : ℝ)^19 ≤ (4424532300953/12500000000000 : ℝ)^15 := by
    have hnat : (4404673311 : ℕ)^19*12500000000000^15 ≤ 4424532300953^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404673311 10000000000 4424532300953 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2378597337/5000000000 : ℝ)^19 ≤ (1219442121189/3125000000000 : ℝ)^15 := by
    have hnat : (2378597337 : ℕ)^19*3125000000000^15 ≤ 1219442121189^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2378597337 5000000000 1219442121189 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704293639/5000000000 : ℝ)^19 ≤ (5116318741079/20000000000000 : ℝ)^15 := by
    have hnat : (1704293639 : ℕ)^19*20000000000000^15 ≤ 5116318741079^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704293639 5000000000 5116318741079 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4404673311/10000000000 : ℝ), (2378597337/5000000000 : ℝ), (1704293639/5000000000 : ℝ)] ![(4424532300953/12500000000000 : ℝ), (1219442121189/3125000000000 : ℝ), (5116318741079/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4404673311/10000000000 : ℝ)|^19 ≤ (4424532300953/12500000000000 : ℝ)^15
        have hw : |(4404673311/10000000000 : ℝ)|=(4404673311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2378597337/5000000000 : ℝ)|^19 ≤ (1219442121189/3125000000000 : ℝ)^15
        have hw : |(2378597337/5000000000 : ℝ)|=(2378597337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1704293639/5000000000 : ℝ)|^19 ≤ (5116318741079/20000000000000 : ℝ)^15
        have hw : |(1704293639/5000000000 : ℝ)|=(1704293639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-186050641/625000000 : ℝ)*x 0 + (710086193/1250000000 : ℝ)*x 1 + (764872189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (186050641/625000000 : ℝ)^19 ≤ (21548553753941/100000000000000 : ℝ)^15 := by
    have hnat : (186050641 : ℕ)^19*100000000000000^15 ≤ 21548553753941^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186050641 625000000 21548553753941 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (710086193/1250000000 : ℝ)^19 ≤ (48854885898179/100000000000000 : ℝ)^15 := by
    have hnat : (710086193 : ℕ)^19*100000000000000^15 ≤ 48854885898179^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710086193 1250000000 48854885898179 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764872189/2000000000 : ℝ)^19 ≤ (29596560334967/100000000000000 : ℝ)^15 := by
    have hnat : (764872189 : ℕ)^19*100000000000000^15 ≤ 29596560334967^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764872189 2000000000 29596560334967 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-186050641/625000000 : ℝ), (710086193/1250000000 : ℝ), (764872189/2000000000 : ℝ)] ![(21548553753941/100000000000000 : ℝ), (48854885898179/100000000000000 : ℝ), (29596560334967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-186050641/625000000 : ℝ)|^19 ≤ (21548553753941/100000000000000 : ℝ)^15
        have hw : |(-186050641/625000000 : ℝ)|=(186050641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(710086193/1250000000 : ℝ)|^19 ≤ (48854885898179/100000000000000 : ℝ)^15
        have hw : |(710086193/1250000000 : ℝ)|=(710086193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(764872189/2000000000 : ℝ)|^19 ≤ (29596560334967/100000000000000 : ℝ)^15
        have hw : |(764872189/2000000000 : ℝ)|=(764872189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1318689681/2000000000 : ℝ)*x 0 + (-89389661/10000000000 : ℝ)*x 1 + (123050767/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318689681/2000000000 : ℝ)^19 ≤ (59003255616711/100000000000000 : ℝ)^15 := by
    have hnat : (1318689681 : ℕ)^19*100000000000000^15 ≤ 59003255616711^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318689681 2000000000 59003255616711 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89389661/10000000000 : ℝ)^19 ≤ (254076150613/100000000000000 : ℝ)^15 := by
    have hnat : (89389661 : ℕ)^19*100000000000000^15 ≤ 254076150613^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89389661 10000000000 254076150613 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123050767/250000000 : ℝ)^19 ≤ (8148533646033/20000000000000 : ℝ)^15 := by
    have hnat : (123050767 : ℕ)^19*20000000000000^15 ≤ 8148533646033^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123050767 250000000 8148533646033 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318689681/2000000000 : ℝ), (-89389661/10000000000 : ℝ), (123050767/250000000 : ℝ)] ![(59003255616711/100000000000000 : ℝ), (254076150613/100000000000000 : ℝ), (8148533646033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318689681/2000000000 : ℝ)|^19 ≤ (59003255616711/100000000000000 : ℝ)^15
        have hw : |(1318689681/2000000000 : ℝ)|=(1318689681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89389661/10000000000 : ℝ)|^19 ≤ (254076150613/100000000000000 : ℝ)^15
        have hw : |(-89389661/10000000000 : ℝ)|=(89389661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(123050767/250000000 : ℝ)|^19 ≤ (8148533646033/20000000000000 : ℝ)^15
        have hw : |(123050767/250000000 : ℝ)|=(123050767/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (64348367/250000000 : ℝ)*x 0 + (1291363283/2000000000 : ℝ)*x 1 + (-413347443/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64348367/250000000 : ℝ)^19 ≤ (17923529175207/100000000000000 : ℝ)^15 := by
    have hnat : (64348367 : ℕ)^19*100000000000000^15 ≤ 17923529175207^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64348367 250000000 17923529175207 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291363283/2000000000 : ℝ)^19 ≤ (28729409057707/50000000000000 : ℝ)^15 := by
    have hnat : (1291363283 : ℕ)^19*50000000000000^15 ≤ 28729409057707^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291363283 2000000000 28729409057707 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413347443/1250000000 : ℝ)^19 ≤ (12308826346677/50000000000000 : ℝ)^15 := by
    have hnat : (413347443 : ℕ)^19*50000000000000^15 ≤ 12308826346677^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413347443 1250000000 12308826346677 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64348367/250000000 : ℝ), (1291363283/2000000000 : ℝ), (-413347443/1250000000 : ℝ)] ![(17923529175207/100000000000000 : ℝ), (28729409057707/50000000000000 : ℝ), (12308826346677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64348367/250000000 : ℝ)|^19 ≤ (17923529175207/100000000000000 : ℝ)^15
        have hw : |(64348367/250000000 : ℝ)|=(64348367/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1291363283/2000000000 : ℝ)|^19 ≤ (28729409057707/50000000000000 : ℝ)^15
        have hw : |(1291363283/2000000000 : ℝ)|=(1291363283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413347443/1250000000 : ℝ)|^19 ≤ (12308826346677/50000000000000 : ℝ)^15
        have hw : |(-413347443/1250000000 : ℝ)|=(413347443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315080_s1_s1_25 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (465414009/1000000000 : ℝ)*x 0 + (4447947339/10000000000 : ℝ)*x 1 + (694866143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (465414009/1000000000 : ℝ)^19 ≤ (37954502675851/100000000000000 : ℝ)^15 := by
    have hnat : (465414009 : ℕ)^19*100000000000000^15 ≤ 37954502675851^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465414009 1000000000 37954502675851 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4447947339/10000000000 : ℝ)^19 ≤ (1433492850643/4000000000000 : ℝ)^15 := by
    have hnat : (4447947339 : ℕ)^19*4000000000000^15 ≤ 1433492850643^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4447947339 10000000000 1433492850643 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694866143/2000000000 : ℝ)^19 ≤ (26208176042781/100000000000000 : ℝ)^15 := by
    have hnat : (694866143 : ℕ)^19*100000000000000^15 ≤ 26208176042781^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694866143 2000000000 26208176042781 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(465414009/1000000000 : ℝ), (4447947339/10000000000 : ℝ), (694866143/2000000000 : ℝ)] ![(37954502675851/100000000000000 : ℝ), (1433492850643/4000000000000 : ℝ), (26208176042781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(465414009/1000000000 : ℝ)|^19 ≤ (37954502675851/100000000000000 : ℝ)^15
        have hw : |(465414009/1000000000 : ℝ)|=(465414009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4447947339/10000000000 : ℝ)|^19 ≤ (1433492850643/4000000000000 : ℝ)^15
        have hw : |(4447947339/10000000000 : ℝ)|=(4447947339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(694866143/2000000000 : ℝ)|^19 ≤ (26208176042781/100000000000000 : ℝ)^15
        have hw : |(694866143/2000000000 : ℝ)|=(694866143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315080_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((18431/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18431/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((45639/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(45639/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79119/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79119/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27137/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27137/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((877/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(877/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(789/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(789/2500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (18431/25000 : ℝ) ^ (75/16 : ℝ) ≤ (23956130707242720049/100000000000000000000 : ℝ) := by
    have hpowers : (18431/25000 : ℝ)^75 ≤ (23956130707242720049/100000000000000000000 : ℝ)^16 := by
      have hnat : (18431 : ℕ)^75*100000000000000000000^16 ≤ 23956130707242720049^16*25000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18431 25000 23956130707242720049 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18431/25000 : ℝ)) (X := (23956130707242720049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (123956130707242720049/100000000000000000000 : ℝ) ≤ (5234403287760853/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (123956130707242720049/100000000000000000000 : ℝ)^16 ≤ (5234403287760853/5000000000000000 : ℝ)^75 := by
      have hnat : (123956130707242720049 : ℕ)^16*5000000000000000^75 ≤ 5234403287760853^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123956130707242720049 100000000000000000000 5234403287760853 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5234403287760853/5000000000000000 : ℝ)) (X := (123956130707242720049/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (73956130707242720049/50000000000000000000 : ℝ) ≤ (10870951489671987/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (73956130707242720049/50000000000000000000 : ℝ)^16 ≤ (10870951489671987/10000000000000000 : ℝ)^75 := by
      have hnat : (73956130707242720049 : ℕ)^16*10000000000000000^75 ≤ 10870951489671987^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73956130707242720049 50000000000000000000 10870951489671987 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10870951489671987/10000000000000000 : ℝ)) (X := (73956130707242720049/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(234403287760853/3686200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(402144914150281/7372400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (18431/25000 : ℝ)) (alpha := (234403287760853/3686200000000000 : ℝ)) (beta := (402144914150281/7372400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18431/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(234403287760853/3686200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(402144914150281/7372400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (45639/100000 : ℝ) ^ (75/16 : ℝ) ≤ (15813138683780053/625000000000000000 : ℝ) := by
    have hpowers : (45639/100000 : ℝ)^75 ≤ (15813138683780053/625000000000000000 : ℝ)^16 := by
      have hnat : (45639 : ℕ)^75*625000000000000000^16 ≤ 15813138683780053^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45639 100000 15813138683780053 625000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45639/100000 : ℝ)) (X := (15813138683780053/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (640813138683780053/625000000000000000 : ℝ) ≤ (10053446317232131/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (640813138683780053/625000000000000000 : ℝ)^16 ≤ (10053446317232131/10000000000000000 : ℝ)^75 := by
      have hnat : (640813138683780053 : ℕ)^16*10000000000000000^75 ≤ 10053446317232131^75*625000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        640813138683780053 625000000000000000 10053446317232131 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10053446317232131/10000000000000000 : ℝ)) (X := (640813138683780053/625000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (328313138683780053/312500000000000000 : ℝ) ≤ (10105864979021923/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (328313138683780053/312500000000000000 : ℝ)^16 ≤ (10105864979021923/10000000000000000 : ℝ)^75 := by
      have hnat : (328313138683780053 : ℕ)^16*10000000000000000^75 ≤ 10105864979021923^75*312500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        328313138683780053 312500000000000000 10105864979021923 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10105864979021923/10000000000000000 : ℝ)) (X := (328313138683780053/312500000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(5938479692459/507100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(546027726977/47540625000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (45639/100000 : ℝ)) (alpha := (5938479692459/507100000000000 : ℝ)) (beta := (546027726977/47540625000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (45639/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(5938479692459/507100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(546027726977/47540625000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (79119/100000 : ℝ) ^ (75/16 : ℝ) ≤ (8339330951509519959/25000000000000000000 : ℝ) := by
    have hpowers : (79119/100000 : ℝ)^75 ≤ (8339330951509519959/25000000000000000000 : ℝ)^16 := by
      have hnat : (79119 : ℕ)^75*25000000000000000000^16 ≤ 8339330951509519959^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79119 100000 8339330951509519959 25000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79119/100000 : ℝ)) (X := (8339330951509519959/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (33339330951509519959/25000000000000000000 : ℝ) ≤ (2126670768226353/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (33339330951509519959/25000000000000000000 : ℝ)^16 ≤ (2126670768226353/2000000000000000 : ℝ)^75 := by
      have hnat : (33339330951509519959 : ℕ)^16*2000000000000000^75 ≤ 2126670768226353^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33339330951509519959 25000000000000000000 2126670768226353 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2126670768226353/2000000000000000 : ℝ)) (X := (33339330951509519959/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (20839330951509519959/12500000000000000000 : ℝ) ≤ (5576021070725851/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (20839330951509519959/12500000000000000000 : ℝ)^16 ≤ (5576021070725851/5000000000000000 : ℝ)^75 := by
      have hnat : (20839330951509519959 : ℕ)^16*5000000000000000^75 ≤ 5576021070725851^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20839330951509519959 12500000000000000000 5576021070725851 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5576021070725851/5000000000000000 : ℝ)) (X := (20839330951509519959/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(126670768226353/1582380000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(518688300319937/7911900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (79119/100000 : ℝ)) (alpha := (126670768226353/1582380000000000 : ℝ)) (beta := (518688300319937/7911900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (79119/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(126670768226353/1582380000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(518688300319937/7911900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3342306409/10000000000 : ℝ)*X 0 0+(5485425307/10000000000 : ℝ)*X 0 1+(738485489/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((237219939/400000000 : ℝ)*X 1 0+(-556526623/10000000000 : ℝ)*X 1 1+(1080268501/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((48115803/156250000 : ℝ)*X 2 0+(745795061/1250000000 : ℝ)*X 2 1+(-42524913/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((503174773/1250000000 : ℝ)*X 0 0+(488588351/1000000000 : ℝ)*X 0 1+(1833113557/5000000000 : ℝ)*X 0 2+(503174773/1250000000 : ℝ)*X 1 0+(488588351/1000000000 : ℝ)*X 1 1+(1833113557/5000000000 : ℝ)*X 1 2+(503174773/1250000000 : ℝ)*X 2 0+(488588351/1000000000 : ℝ)*X 2 1+(1833113557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-3375638643/10000000000 : ℝ)*X 0 0+(5499131781/10000000000 : ℝ)*X 0 1+(911151449/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((721205807/1250000000 : ℝ)*X 1 0+(-6221849/1250000000 : ℝ)*X 1 1+(5790393719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1404744831/5000000000 : ℝ)*X 2 0+(1624107863/2500000000 : ℝ)*X 2 1+(-303334669/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((766437839/2000000000 : ℝ)*X 0 0+(4900603913/10000000000 : ℝ)*X 0 1+(961492373/2500000000 : ℝ)*X 0 2+(766437839/2000000000 : ℝ)*X 1 0+(4900603913/10000000000 : ℝ)*X 1 1+(961492373/2500000000 : ℝ)*X 1 2+(766437839/2000000000 : ℝ)*X 2 0+(4900603913/10000000000 : ℝ)*X 2 1+(961492373/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-3602168887/10000000000 : ℝ)*X 0 0+(5482355939/10000000000 : ℝ)*X 0 1+(3437832113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((181236719/312500000 : ℝ)*X 1 0+(-53125291/1000000000 : ℝ)*X 1 1+(5548345191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2842508147/10000000000 : ℝ)*X 2 0+(594065477/1000000000 : ℝ)*X 2 1+(-3657600899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((4404673311/10000000000 : ℝ)*X 0 0+(2378597337/5000000000 : ℝ)*X 0 1+(1704293639/5000000000 : ℝ)*X 0 2+(4404673311/10000000000 : ℝ)*X 1 0+(2378597337/5000000000 : ℝ)*X 1 1+(1704293639/5000000000 : ℝ)*X 1 2+(4404673311/10000000000 : ℝ)*X 2 0+(2378597337/5000000000 : ℝ)*X 2 1+(1704293639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((-186050641/625000000 : ℝ)*X 0 0+(710086193/1250000000 : ℝ)*X 0 1+(764872189/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((1318689681/2000000000 : ℝ)*X 1 0+(-89389661/10000000000 : ℝ)*X 1 1+(123050767/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((64348367/250000000 : ℝ)*X 2 0+(1291363283/2000000000 : ℝ)*X 2 1+(-413347443/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((465414009/1000000000 : ℝ)*X 0 0+(4447947339/10000000000 : ℝ)*X 0 1+(694866143/2000000000 : ℝ)*X 0 2+(465414009/1000000000 : ℝ)*X 1 0+(4447947339/10000000000 : ℝ)*X 1 1+(694866143/2000000000 : ℝ)*X 1 2+(465414009/1000000000 : ℝ)*X 2 0+(4447947339/10000000000 : ℝ)*X 2 1+(694866143/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315080_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((27137/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27137/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (326568459397569332852574937/18692720200000000000000000000000 : ℝ) := by norm_num
    linear_combination (456836393/8000000000 : ℝ)*(base40) + (4239678305877/1000000000000 : ℝ)*(base49) + (907621134247/500000000000 : ℝ)*(base50) + (5175579/1000000000000 : ℝ)*(base60) + (7324311498463/1000000000000 : ℝ)*(major_s1_0) + (7324311498463/1000000000000 : ℝ)*(major_s1_1) + (7324311498463/1000000000000 : ℝ)*(major_s1_2) + (2174519883/1000000000000 : ℝ)*(sp_s1_0) + (1306611593311/125000000000 : ℝ)*(sp_s1_7) + (10454937175177/1000000000000 : ℝ)*(sp_s1_8) + (2613781249541/250000000000 : ℝ)*(sp_s1_9) + (4193492175303/1000000000000 : ℝ)*(sp_s1_12) + (187822987/1000000000000 : ℝ)*(sp_s1_14) + (57731793/1000000000000 : ℝ)*(sp_s1_20) + (4193492175303/1000000000000 : ℝ)*(f.failure) + (2613781249541/250000000000 : ℝ)*(f.sum) + (35993506447609177231/40121244900000000000000000000000 : ℝ)*base62 + (6570230757941231/7911900000000000000000000000 : ℝ)*base65 + (379774529780243/507100000000000000000000000 : ℝ)*base67 + (49453862364101/316476000000000000000000000 : ℝ)*base69 + (9538139676539758237/291648457800000000000000000000000 : ℝ)*base70 + (7150125175680663/7372400000000000000000000000 : ℝ)*base73 + (111771724867061/760650000000000000000000000 : ℝ)*base74 + (173412505657399/3686200000000000000000000000 : ℝ)*base77 + (6053494356649232873/7477088080000000000000000000000 : ℝ)*base79 + (53323/100000000000000000 : ℝ)*base86 + (53323/100000000000000000 : ℝ)*base88 + (53323/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((877/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(877/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (178746031914430893948059373019/14938882116200000000000000000000000 : ℝ) := by norm_num
    linear_combination (111423237901/500000000000 : ℝ)*(base40) + (34161545441/31250000000 : ℝ)*(base49) + (2213951/1000000000000 : ℝ)*(base60) + (3306915870933/1000000000000 : ℝ)*(major_s1_0) + (3306915870933/1000000000000 : ℝ)*(major_s1_1) + (3306915870933/1000000000000 : ℝ)*(major_s1_2) + (23267491/1000000000000 : ℝ)*(sp_s1_2) + (70310427/1000000000000 : ℝ)*(sp_s1_6) + (57724259/1000000000000 : ℝ)*(sp_s1_8) + (590059025373/125000000000 : ℝ)*(sp_s1_13) + (188816579149/40000000000 : ℝ)*(sp_s1_14) + (2360224467747/500000000000 : ℝ)*(sp_s1_15) + (37859593443/20000000000 : ℝ)*(sp_s1_19) + (61113583/200000000000 : ℝ)*(sp_s1_25) + (473338887623/250000000000 : ℝ)*(f.failure) + (590059025373/125000000000 : ℝ)*(f.sum) + (1345275633109420627/13373748300000000000000000000000 : ℝ)*base62 + (1489156355685223/2637300000000000000000000000 : ℝ)*base64 + (164171647598697/507100000000000000000000000 : ℝ)*base66 + (63297346446329/527460000000000000000000000 : ℝ)*base68 + (13763903345580062509/97216152600000000000000000000000 : ℝ)*base70 + (4325213901752587/7372400000000000000000000000 : ℝ)*base72 + (96081496780571/126775000000000000000000000 : ℝ)*base74 + (2438363957024811/3686200000000000000000000000 : ℝ)*base76 + (153370609112235553/1495417616000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (20557/25000000000000000 : ℝ)*base87 + (20557/25000000000000000 : ℝ)*base89 + (20557/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(789/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(789/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (84193092629326078135190124787/8355645929400000000000000000000000 : ℝ) := by norm_num
    linear_combination (14166997/1000000000000 : ℝ)*(base15) + (220911395321/250000000000 : ℝ)*(base40) + (136606613577/31250000000 : ℝ)*(base49) + (796154619661/500000000000 : ℝ)*(base50) + (7836703326667/1000000000000 : ℝ)*(major_s1_0) + (7836703326667/1000000000000 : ℝ)*(major_s1_1) + (7836703326667/1000000000000 : ℝ)*(major_s1_2) + (41703721/1000000000000 : ℝ)*(sp_s1_1) + (39413639/250000000000 : ℝ)*(sp_s1_9) + (68776179/1000000000000 : ℝ)*(sp_s1_19) + (2237308828477/200000000000 : ℝ)*(sp_s1_20) + (11186488271667/1000000000000 : ℝ)*(sp_s1_21) + (11186386487829/1000000000000 : ℝ)*(sp_s1_22) + (1121697594009/250000000000 : ℝ)*(sp_s1_25) + (897371830443/200000000000 : ℝ)*(f.failure) + (2237308828477/200000000000 : ℝ)*(f.sum) + (442388010465177131/680021100000000000000000000000 : ℝ)*base62 + (33973878013981/134100000000000000000000000 : ℝ)*base65 + (303936817413677/507100000000000000000000000 : ℝ)*base67 + (9242215369931/26820000000000000000000000 : ℝ)*base69 + (992824593943373113/4943194200000000000000000000000 : ℝ)*base71 + (1259220799515653/7372400000000000000000000000 : ℝ)*base72 + (245761391467109/760650000000000000000000000 : ℝ)*base74 + (2045002619808811/3686200000000000000000000000 : ℝ)*base77 + (304129606332283379/7477088080000000000000000000000 : ℝ)*base78 + (3937/20000000000000000 : ℝ)*base87 + (3937/20000000000000000 : ℝ)*base89 + (3937/20000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((18431/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18431/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((45639/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(45639/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79119/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79119/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27137/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27137/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((877/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(877/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(789/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(789/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315080_s1 p hpa hpb X hX hprev0

#print axioms solution

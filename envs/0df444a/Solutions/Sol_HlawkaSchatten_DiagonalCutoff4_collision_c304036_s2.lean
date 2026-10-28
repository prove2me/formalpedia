-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304036_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:38:56.629029+00:00
-- url     : https://prove2.me/submissions/34e4b9f0-e104-4481-a196-fcf5dd774588

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
theorem collision_support_c304036_s2_s2_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-43432447/625000000 : ℝ)*x 0 + (-719141827/1250000000 : ℝ)*x 1 + (-2870973741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43432447/625000000 : ℝ)^17 ≤ (1529594706001/50000000000000 : ℝ)^13 := by
    have hnat : (43432447 : ℕ)^17*50000000000000^13 ≤ 1529594706001^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43432447 625000000 1529594706001 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (719141827/1250000000 : ℝ)^17 ≤ (12133022902829/25000000000000 : ℝ)^13 := by
    have hnat : (719141827 : ℕ)^17*25000000000000^13 ≤ 12133022902829^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719141827 1250000000 12133022902829 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2870973741/5000000000 : ℝ)^17 ≤ (9681743792949/20000000000000 : ℝ)^13 := by
    have hnat : (2870973741 : ℕ)^17*20000000000000^13 ≤ 9681743792949^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2870973741 5000000000 9681743792949 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43432447/625000000 : ℝ), (-719141827/1250000000 : ℝ), (-2870973741/5000000000 : ℝ)] ![(1529594706001/50000000000000 : ℝ), (12133022902829/25000000000000 : ℝ), (9681743792949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43432447/625000000 : ℝ)|^17 ≤ (1529594706001/50000000000000 : ℝ)^13
        have hw : |(-43432447/625000000 : ℝ)|=(43432447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-719141827/1250000000 : ℝ)|^17 ≤ (12133022902829/25000000000000 : ℝ)^13
        have hw : |(-719141827/1250000000 : ℝ)|=(719141827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2870973741/5000000000 : ℝ)|^17 ≤ (9681743792949/20000000000000 : ℝ)^13
        have hw : |(-2870973741/5000000000 : ℝ)|=(2870973741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (332674057/625000000 : ℝ)*x 0 + (-757942681/2000000000 : ℝ)*x 1 + (-3782344199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332674057/625000000 : ℝ)^17 ≤ (43840345548499/100000000000000 : ℝ)^13 := by
    have hnat : (332674057 : ℕ)^17*100000000000000^13 ≤ 43840345548499^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332674057 625000000 43840345548499 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757942681/2000000000 : ℝ)^17 ≤ (14057781641373/50000000000000 : ℝ)^13 := by
    have hnat : (757942681 : ℕ)^17*50000000000000^13 ≤ 14057781641373^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757942681 2000000000 14057781641373 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3782344199/10000000000 : ℝ)^17 ≤ (438188924361/1562500000000 : ℝ)^13 := by
    have hnat : (3782344199 : ℕ)^17*1562500000000^13 ≤ 438188924361^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3782344199 10000000000 438188924361 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332674057/625000000 : ℝ), (-757942681/2000000000 : ℝ), (-3782344199/10000000000 : ℝ)] ![(43840345548499/100000000000000 : ℝ), (14057781641373/50000000000000 : ℝ), (438188924361/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332674057/625000000 : ℝ)|^17 ≤ (43840345548499/100000000000000 : ℝ)^13
        have hw : |(332674057/625000000 : ℝ)|=(332674057/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-757942681/2000000000 : ℝ)|^17 ≤ (14057781641373/50000000000000 : ℝ)^13
        have hw : |(-757942681/2000000000 : ℝ)|=(757942681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3782344199/10000000000 : ℝ)|^17 ≤ (438188924361/1562500000000 : ℝ)^13
        have hw : |(-3782344199/10000000000 : ℝ)|=(3782344199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-279308507/5000000000 : ℝ)*x 0 + (-3229219327/5000000000 : ℝ)*x 1 + (-5080122703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279308507/5000000000 : ℝ)^17 ≤ (91975215629/4000000000000 : ℝ)^13 := by
    have hnat : (279308507 : ℕ)^17*4000000000000^13 ≤ 91975215629^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279308507 5000000000 91975215629 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3229219327/5000000000 : ℝ)^17 ≤ (1129107360831/2000000000000 : ℝ)^13 := by
    have hnat : (3229219327 : ℕ)^17*2000000000000^13 ≤ 1129107360831^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3229219327 5000000000 1129107360831 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080122703/10000000000 : ℝ)^17 ≤ (20622625775797/50000000000000 : ℝ)^13 := by
    have hnat : (5080122703 : ℕ)^17*50000000000000^13 ≤ 20622625775797^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080122703 10000000000 20622625775797 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-279308507/5000000000 : ℝ), (-3229219327/5000000000 : ℝ), (-5080122703/10000000000 : ℝ)] ![(91975215629/4000000000000 : ℝ), (1129107360831/2000000000000 : ℝ), (20622625775797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-279308507/5000000000 : ℝ)|^17 ≤ (91975215629/4000000000000 : ℝ)^13
        have hw : |(-279308507/5000000000 : ℝ)|=(279308507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3229219327/5000000000 : ℝ)|^17 ≤ (1129107360831/2000000000000 : ℝ)^13
        have hw : |(-3229219327/5000000000 : ℝ)|=(3229219327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5080122703/10000000000 : ℝ)|^17 ≤ (20622625775797/50000000000000 : ℝ)^13
        have hw : |(-5080122703/10000000000 : ℝ)|=(5080122703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (316255221/625000000 : ℝ)*x 0 + (550077271/1250000000 : ℝ)*x 1 + (-1720592791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (316255221/625000000 : ℝ)^17 ≤ (2564538951921/6250000000000 : ℝ)^13 := by
    have hnat : (316255221 : ℕ)^17*6250000000000^13 ≤ 2564538951921^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316255221 625000000 2564538951921 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550077271/1250000000 : ℝ)^17 ≤ (2136513338839/6250000000000 : ℝ)^13 := by
    have hnat : (550077271 : ℕ)^17*6250000000000^13 ≤ 2136513338839^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550077271 1250000000 2136513338839 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1720592791/5000000000 : ℝ)^17 ≤ (12391581666617/50000000000000 : ℝ)^13 := by
    have hnat : (1720592791 : ℕ)^17*50000000000000^13 ≤ 12391581666617^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720592791 5000000000 12391581666617 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(316255221/625000000 : ℝ), (550077271/1250000000 : ℝ), (-1720592791/5000000000 : ℝ)] ![(2564538951921/6250000000000 : ℝ), (2136513338839/6250000000000 : ℝ), (12391581666617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(316255221/625000000 : ℝ)|^17 ≤ (2564538951921/6250000000000 : ℝ)^13
        have hw : |(316255221/625000000 : ℝ)|=(316255221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550077271/1250000000 : ℝ)|^17 ≤ (2136513338839/6250000000000 : ℝ)^13
        have hw : |(550077271/1250000000 : ℝ)|=(550077271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1720592791/5000000000 : ℝ)|^17 ≤ (12391581666617/50000000000000 : ℝ)^13
        have hw : |(-1720592791/5000000000 : ℝ)|=(1720592791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5871991821/10000000000 : ℝ)*x 0 + (-317052881/1250000000 : ℝ)*x 1 + (4335288539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5871991821/10000000000 : ℝ)^17 ≤ (49847398883171/100000000000000 : ℝ)^13 := by
    have hnat : (5871991821 : ℕ)^17*100000000000000^13 ≤ 49847398883171^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5871991821 10000000000 49847398883171 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317052881/1250000000 : ℝ)^17 ≤ (207881241143/1250000000000 : ℝ)^13 := by
    have hnat : (317052881 : ℕ)^17*1250000000000^13 ≤ 207881241143^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317052881 1250000000 207881241143 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4335288539/10000000000 : ℝ)^17 ≤ (33522101810511/100000000000000 : ℝ)^13 := by
    have hnat : (4335288539 : ℕ)^17*100000000000000^13 ≤ 33522101810511^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335288539 10000000000 33522101810511 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5871991821/10000000000 : ℝ), (-317052881/1250000000 : ℝ), (4335288539/10000000000 : ℝ)] ![(49847398883171/100000000000000 : ℝ), (207881241143/1250000000000 : ℝ), (33522101810511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5871991821/10000000000 : ℝ)|^17 ≤ (49847398883171/100000000000000 : ℝ)^13
        have hw : |(5871991821/10000000000 : ℝ)|=(5871991821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-317052881/1250000000 : ℝ)|^17 ≤ (207881241143/1250000000000 : ℝ)^13
        have hw : |(-317052881/1250000000 : ℝ)|=(317052881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4335288539/10000000000 : ℝ)|^17 ≤ (33522101810511/100000000000000 : ℝ)^13
        have hw : |(4335288539/10000000000 : ℝ)|=(4335288539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5554032877/10000000000 : ℝ)*x 0 + (-3095494339/10000000000 : ℝ)*x 1 + (-209564137/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5554032877/10000000000 : ℝ)^17 ≤ (46347512438473/100000000000000 : ℝ)^13 := by
    have hnat : (5554032877 : ℕ)^17*100000000000000^13 ≤ 46347512438473^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5554032877 10000000000 46347512438473 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3095494339/10000000000 : ℝ)^17 ≤ (2697376502441/12500000000000 : ℝ)^13 := by
    have hnat : (3095494339 : ℕ)^17*12500000000000^13 ≤ 2697376502441^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3095494339 10000000000 2697376502441 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209564137/500000000 : ℝ)^17 ≤ (6414695104853/20000000000000 : ℝ)^13 := by
    have hnat : (209564137 : ℕ)^17*20000000000000^13 ≤ 6414695104853^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209564137 500000000 6414695104853 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5554032877/10000000000 : ℝ), (-3095494339/10000000000 : ℝ), (-209564137/500000000 : ℝ)] ![(46347512438473/100000000000000 : ℝ), (2697376502441/12500000000000 : ℝ), (6414695104853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5554032877/10000000000 : ℝ)|^17 ≤ (46347512438473/100000000000000 : ℝ)^13
        have hw : |(5554032877/10000000000 : ℝ)|=(5554032877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3095494339/10000000000 : ℝ)|^17 ≤ (2697376502441/12500000000000 : ℝ)^13
        have hw : |(-3095494339/10000000000 : ℝ)|=(3095494339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209564137/500000000 : ℝ)|^17 ≤ (6414695104853/20000000000000 : ℝ)^13
        have hw : |(-209564137/500000000 : ℝ)|=(209564137/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (717/10000000000 : ℝ)*x 0 + (-5654020407/10000000000 : ℝ)*x 1 + (-1528668057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (717/10000000000 : ℝ)^17 ≤ (45417/100000000000000 : ℝ)^13 := by
    have hnat : (717 : ℕ)^17*100000000000000^13 ≤ 45417^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717 10000000000 45417 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5654020407/10000000000 : ℝ)^17 ≤ (1897665364927/4000000000000 : ℝ)^13 := by
    have hnat : (5654020407 : ℕ)^17*4000000000000^13 ≤ 1897665364927^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654020407 10000000000 1897665364927 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1528668057/2500000000 : ℝ)^17 ≤ (26279182909599/50000000000000 : ℝ)^13 := by
    have hnat : (1528668057 : ℕ)^17*50000000000000^13 ≤ 26279182909599^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528668057 2500000000 26279182909599 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(717/10000000000 : ℝ), (-5654020407/10000000000 : ℝ), (-1528668057/2500000000 : ℝ)] ![(45417/100000000000000 : ℝ), (1897665364927/4000000000000 : ℝ), (26279182909599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(717/10000000000 : ℝ)|^17 ≤ (45417/100000000000000 : ℝ)^13
        have hw : |(717/10000000000 : ℝ)|=(717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5654020407/10000000000 : ℝ)|^17 ≤ (1897665364927/4000000000000 : ℝ)^13
        have hw : |(-5654020407/10000000000 : ℝ)|=(5654020407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1528668057/2500000000 : ℝ)|^17 ≤ (26279182909599/50000000000000 : ℝ)^13
        have hw : |(-1528668057/2500000000 : ℝ)|=(1528668057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (678968951/1250000000 : ℝ)*x 0 + (1782113677/5000000000 : ℝ)*x 1 + (-121375877/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (678968951/1250000000 : ℝ)^17 ≤ (45017663259871/100000000000000 : ℝ)^13 := by
    have hnat : (678968951 : ℕ)^17*100000000000000^13 ≤ 45017663259871^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678968951 1250000000 45017663259871 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1782113677/5000000000 : ℝ)^17 ≤ (25948281371381/100000000000000 : ℝ)^13 := by
    have hnat : (1782113677 : ℕ)^17*100000000000000^13 ≤ 25948281371381^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782113677 5000000000 25948281371381 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121375877/312500000 : ℝ)^17 ≤ (29034055357793/100000000000000 : ℝ)^13 := by
    have hnat : (121375877 : ℕ)^17*100000000000000^13 ≤ 29034055357793^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121375877 312500000 29034055357793 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(678968951/1250000000 : ℝ), (1782113677/5000000000 : ℝ), (-121375877/312500000 : ℝ)] ![(45017663259871/100000000000000 : ℝ), (25948281371381/100000000000000 : ℝ), (29034055357793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(678968951/1250000000 : ℝ)|^17 ≤ (45017663259871/100000000000000 : ℝ)^13
        have hw : |(678968951/1250000000 : ℝ)|=(678968951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1782113677/5000000000 : ℝ)|^17 ≤ (25948281371381/100000000000000 : ℝ)^13
        have hw : |(1782113677/5000000000 : ℝ)|=(1782113677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121375877/312500000 : ℝ)|^17 ≤ (29034055357793/100000000000000 : ℝ)^13
        have hw : |(-121375877/312500000 : ℝ)|=(121375877/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6777608223/10000000000 : ℝ)*x 0 + (-2787532553/10000000000 : ℝ)*x 1 + (3037644233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6777608223/10000000000 : ℝ)^17 ≤ (60131216143633/100000000000000 : ℝ)^13 := by
    have hnat : (6777608223 : ℕ)^17*100000000000000^13 ≤ 60131216143633^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6777608223 10000000000 60131216143633 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2787532553/10000000000 : ℝ)^17 ≤ (94078069631/500000000000 : ℝ)^13 := by
    have hnat : (2787532553 : ℕ)^17*500000000000^13 ≤ 94078069631^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787532553 10000000000 94078069631 500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3037644233/10000000000 : ℝ)^17 ≤ (2105316990459/10000000000000 : ℝ)^13 := by
    have hnat : (3037644233 : ℕ)^17*10000000000000^13 ≤ 2105316990459^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3037644233 10000000000 2105316990459 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6777608223/10000000000 : ℝ), (-2787532553/10000000000 : ℝ), (3037644233/10000000000 : ℝ)] ![(60131216143633/100000000000000 : ℝ), (94078069631/500000000000 : ℝ), (2105316990459/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6777608223/10000000000 : ℝ)|^17 ≤ (60131216143633/100000000000000 : ℝ)^13
        have hw : |(6777608223/10000000000 : ℝ)|=(6777608223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2787532553/10000000000 : ℝ)|^17 ≤ (94078069631/500000000000 : ℝ)^13
        have hw : |(-2787532553/10000000000 : ℝ)|=(2787532553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3037644233/10000000000 : ℝ)|^17 ≤ (2105316990459/10000000000000 : ℝ)^13
        have hw : |(3037644233/10000000000 : ℝ)|=(3037644233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_19 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5507388139/10000000000 : ℝ)*x 0 + (-221098111/625000000 : ℝ)*x 1 + (-765157467/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5507388139/10000000000 : ℝ)^17 ≤ (5729895188511/12500000000000 : ℝ)^13 := by
    have hnat : (5507388139 : ℕ)^17*12500000000000^13 ≤ 5729895188511^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507388139 10000000000 5729895188511 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221098111/625000000 : ℝ)^17 ≤ (25694786846307/100000000000000 : ℝ)^13 := by
    have hnat : (221098111 : ℕ)^17*100000000000000^13 ≤ 25694786846307^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221098111 625000000 25694786846307 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (765157467/2000000000 : ℝ)^17 ≤ (3558256454897/12500000000000 : ℝ)^13 := by
    have hnat : (765157467 : ℕ)^17*12500000000000^13 ≤ 3558256454897^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765157467 2000000000 3558256454897 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5507388139/10000000000 : ℝ), (-221098111/625000000 : ℝ), (-765157467/2000000000 : ℝ)] ![(5729895188511/12500000000000 : ℝ), (25694786846307/100000000000000 : ℝ), (3558256454897/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5507388139/10000000000 : ℝ)|^17 ≤ (5729895188511/12500000000000 : ℝ)^13
        have hw : |(5507388139/10000000000 : ℝ)|=(5507388139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221098111/625000000 : ℝ)|^17 ≤ (25694786846307/100000000000000 : ℝ)^13
        have hw : |(-221098111/625000000 : ℝ)|=(221098111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-765157467/2000000000 : ℝ)|^17 ≤ (3558256454897/12500000000000 : ℝ)^13
        have hw : |(-765157467/2000000000 : ℝ)|=(765157467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (77/1250000000 : ℝ)*x 0 + (-6123865453/10000000000 : ℝ)*x 1 + (-5644598343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77/1250000000 : ℝ)^17 ≤ (37239/100000000000000 : ℝ)^13 := by
    have hnat : (77 : ℕ)^17*100000000000000^13 ≤ 37239^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77 1250000000 37239 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6123865453/10000000000 : ℝ)^17 ≤ (26330861723969/50000000000000 : ℝ)^13 := by
    have hnat : (6123865453 : ℕ)^17*50000000000000^13 ≤ 26330861723969^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6123865453 10000000000 26330861723969 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5644598343/10000000000 : ℝ)^17 ≤ (23669138253071/50000000000000 : ℝ)^13 := by
    have hnat : (5644598343 : ℕ)^17*50000000000000^13 ≤ 23669138253071^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5644598343 10000000000 23669138253071 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(77/1250000000 : ℝ), (-6123865453/10000000000 : ℝ), (-5644598343/10000000000 : ℝ)] ![(37239/100000000000000 : ℝ), (26330861723969/50000000000000 : ℝ), (23669138253071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(77/1250000000 : ℝ)|^17 ≤ (37239/100000000000000 : ℝ)^13
        have hw : |(77/1250000000 : ℝ)|=(77/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6123865453/10000000000 : ℝ)|^17 ≤ (26330861723969/50000000000000 : ℝ)^13
        have hw : |(-6123865453/10000000000 : ℝ)|=(6123865453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5644598343/10000000000 : ℝ)|^17 ≤ (23669138253071/50000000000000 : ℝ)^13
        have hw : |(-5644598343/10000000000 : ℝ)|=(5644598343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6793277473/10000000000 : ℝ)*x 0 + (3022414927/10000000000 : ℝ)*x 1 + (-2782553561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6793277473/10000000000 : ℝ)^17 ≤ (12062614766281/20000000000000 : ℝ)^13 := by
    have hnat : (6793277473 : ℕ)^17*20000000000000^13 ≤ 12062614766281^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6793277473 10000000000 12062614766281 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3022414927/10000000000 : ℝ)^17 ≤ (10457624392347/50000000000000 : ℝ)^13 := by
    have hnat : (3022414927 : ℕ)^17*50000000000000^13 ≤ 10457624392347^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3022414927 10000000000 10457624392347 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2782553561/10000000000 : ℝ)^17 ≤ (18771677367751/100000000000000 : ℝ)^13 := by
    have hnat : (2782553561 : ℕ)^17*100000000000000^13 ≤ 18771677367751^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782553561 10000000000 18771677367751 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6793277473/10000000000 : ℝ), (3022414927/10000000000 : ℝ), (-2782553561/10000000000 : ℝ)] ![(12062614766281/20000000000000 : ℝ), (10457624392347/50000000000000 : ℝ), (18771677367751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6793277473/10000000000 : ℝ)|^17 ≤ (12062614766281/20000000000000 : ℝ)^13
        have hw : |(6793277473/10000000000 : ℝ)|=(6793277473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3022414927/10000000000 : ℝ)|^17 ≤ (10457624392347/50000000000000 : ℝ)^13
        have hw : |(3022414927/10000000000 : ℝ)|=(3022414927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2782553561/10000000000 : ℝ)|^17 ≤ (18771677367751/100000000000000 : ℝ)^13
        have hw : |(-2782553561/10000000000 : ℝ)|=(2782553561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (676796783/1250000000 : ℝ)*x 0 + (-1944119587/5000000000 : ℝ)*x 1 + (143186611/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676796783/1250000000 : ℝ)^17 ≤ (4482942060063/10000000000000 : ℝ)^13 := by
    have hnat : (676796783 : ℕ)^17*10000000000000^13 ≤ 4482942060063^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676796783 1250000000 4482942060063 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944119587/5000000000 : ℝ)^17 ≤ (29075227163371/100000000000000 : ℝ)^13 := by
    have hnat : (1944119587 : ℕ)^17*100000000000000^13 ≤ 29075227163371^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944119587 5000000000 29075227163371 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143186611/400000000 : ℝ)^17 ≤ (13047676109471/50000000000000 : ℝ)^13 := by
    have hnat : (143186611 : ℕ)^17*50000000000000^13 ≤ 13047676109471^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143186611 400000000 13047676109471 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676796783/1250000000 : ℝ), (-1944119587/5000000000 : ℝ), (143186611/400000000 : ℝ)] ![(4482942060063/10000000000000 : ℝ), (29075227163371/100000000000000 : ℝ), (13047676109471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676796783/1250000000 : ℝ)|^17 ≤ (4482942060063/10000000000000 : ℝ)^13
        have hw : |(676796783/1250000000 : ℝ)|=(676796783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1944119587/5000000000 : ℝ)|^17 ≤ (29075227163371/100000000000000 : ℝ)^13
        have hw : |(-1944119587/5000000000 : ℝ)|=(1944119587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(143186611/400000000 : ℝ)|^17 ≤ (13047676109471/50000000000000 : ℝ)^13
        have hw : |(143186611/400000000 : ℝ)|=(143186611/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s2_s2_25 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2755437461/5000000000 : ℝ)*x 0 + (-76589717/200000000 : ℝ)*x 1 + (-3529781909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755437461/5000000000 : ℝ)^17 ≤ (22938558025329/50000000000000 : ℝ)^13 := by
    have hnat : (2755437461 : ℕ)^17*50000000000000^13 ≤ 22938558025329^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755437461 5000000000 22938558025329 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76589717/200000000 : ℝ)^17 ≤ (28502043469587/100000000000000 : ℝ)^13 := by
    have hnat : (76589717 : ℕ)^17*100000000000000^13 ≤ 28502043469587^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76589717 200000000 28502043469587 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3529781909/10000000000 : ℝ)^17 ≤ (25620840467789/100000000000000 : ℝ)^13 := by
    have hnat : (3529781909 : ℕ)^17*100000000000000^13 ≤ 25620840467789^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3529781909 10000000000 25620840467789 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755437461/5000000000 : ℝ), (-76589717/200000000 : ℝ), (-3529781909/10000000000 : ℝ)] ![(22938558025329/50000000000000 : ℝ), (28502043469587/100000000000000 : ℝ), (25620840467789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755437461/5000000000 : ℝ)|^17 ≤ (22938558025329/50000000000000 : ℝ)^13
        have hw : |(2755437461/5000000000 : ℝ)|=(2755437461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76589717/200000000 : ℝ)|^17 ≤ (28502043469587/100000000000000 : ℝ)^13
        have hw : |(-76589717/200000000 : ℝ)|=(76589717/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3529781909/10000000000 : ℝ)|^17 ≤ (25620840467789/100000000000000 : ℝ)^13
        have hw : |(-3529781909/10000000000 : ℝ)|=(3529781909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304036_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((15491/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15491/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-73921/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-73921/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-74611/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-74611/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10373/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10373/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42181/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-42181/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8451/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8451/20000 : ℝ)*X 1 2) := by
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
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (15491/50000 : ℝ) ^ (33/8 : ℝ) ≤ (397920656061796863/50000000000000000000 : ℝ) := by
    have hpowers : (15491/50000 : ℝ)^33 ≤ (397920656061796863/50000000000000000000 : ℝ)^8 := by
      have hnat : (15491 : ℕ)^33*50000000000000000000^8 ≤ 397920656061796863^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15491 50000 397920656061796863 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15491/50000 : ℝ)) (X := (397920656061796863/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (50397920656061796863/50000000000000000000 : ℝ) ≤ (80153881858557/80000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50397920656061796863/50000000000000000000 : ℝ)^8 ≤ (80153881858557/80000000000000 : ℝ)^33 := by
      have hnat : (50397920656061796863 : ℕ)^8*80000000000000^33 ≤ 80153881858557^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50397920656061796863 50000000000000000000 80153881858557 80000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80153881858557/80000000000000 : ℝ)) (X := (50397920656061796863/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (25397920656061796863/25000000000000000000 : ℝ) ≤ (1003835575092147/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25397920656061796863/25000000000000000000 : ℝ)^8 ≤ (1003835575092147/1000000000000000 : ℝ)^33 := by
      have hnat : (25397920656061796863 : ℕ)^8*1000000000000000^33 ≤ 1003835575092147^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25397920656061796863 25000000000000000000 1003835575092147 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1003835575092147/1000000000000000 : ℝ)) (X := (25397920656061796863/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(21983122651/3540800000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3824103720369/619640000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (15491/50000 : ℝ)) (alpha := (21983122651/3540800000000 : ℝ)) (beta := (3824103720369/619640000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15491/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(21983122651/3540800000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3824103720369/619640000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (73921/100000 : ℝ) ^ (33/8 : ℝ) ≤ (28751950537700278287/100000000000000000000 : ℝ) := by
    have hpowers : (73921/100000 : ℝ)^33 ≤ (28751950537700278287/100000000000000000000 : ℝ)^8 := by
      have hnat : (73921 : ℕ)^33*100000000000000000000^8 ≤ 28751950537700278287^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73921 100000 28751950537700278287 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73921/100000 : ℝ)) (X := (28751950537700278287/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (128751950537700278287/100000000000000000000 : ℝ) ≤ (10631804594730687/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (128751950537700278287/100000000000000000000 : ℝ)^8 ≤ (10631804594730687/10000000000000000 : ℝ)^33 := by
      have hnat : (128751950537700278287 : ℕ)^8*10000000000000000^33 ≤ 10631804594730687^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        128751950537700278287 100000000000000000000 10631804594730687 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10631804594730687/10000000000000000 : ℝ)) (X := (128751950537700278287/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (78751950537700278287/50000000000000000000 : ℝ) ≤ (5582107577541479/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (78751950537700278287/50000000000000000000 : ℝ)^8 ≤ (5582107577541479/5000000000000000 : ℝ)^33 := by
      have hnat : (78751950537700278287 : ℕ)^8*5000000000000000^33 ≤ 5582107577541479^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78751950537700278287 50000000000000000000 5582107577541479 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5582107577541479/5000000000000000 : ℝ)) (X := (78751950537700278287/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(631804594730687/7392100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(532410560352271/7392100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (73921/100000 : ℝ)) (alpha := (631804594730687/7392100000000000 : ℝ)) (beta := (532410560352271/7392100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (73921/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(631804594730687/7392100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(532410560352271/7392100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (74611/100000 : ℝ) ^ (33/8 : ℝ) ≤ (29875267379582296891/100000000000000000000 : ℝ) := by
    have hpowers : (74611/100000 : ℝ)^33 ≤ (29875267379582296891/100000000000000000000 : ℝ)^8 := by
      have hnat : (74611 : ℕ)^33*100000000000000000000^8 ≤ 29875267379582296891^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74611 100000 29875267379582296891 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74611/100000 : ℝ)) (X := (29875267379582296891/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (129875267379582296891/100000000000000000000 : ℝ) ≤ (5327108827826943/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (129875267379582296891/100000000000000000000 : ℝ)^8 ≤ (5327108827826943/5000000000000000 : ℝ)^33 := by
      have hnat : (129875267379582296891 : ℕ)^8*5000000000000000^33 ≤ 5327108827826943^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        129875267379582296891 100000000000000000000 5327108827826943 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5327108827826943/5000000000000000 : ℝ)) (X := (129875267379582296891/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (79875267379582296891/50000000000000000000 : ℝ) ≤ (2800653360573997/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (79875267379582296891/50000000000000000000 : ℝ)^8 ≤ (2800653360573997/2500000000000000 : ℝ)^33 := by
      have hnat : (79875267379582296891 : ℕ)^8*2500000000000000^33 ≤ 2800653360573997^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79875267379582296891 50000000000000000000 2800653360573997 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2800653360573997/2500000000000000 : ℝ)) (X := (79875267379582296891/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(327108827826943/3730550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(274197893321051/3730550000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (74611/100000 : ℝ)) (alpha := (327108827826943/3730550000000000 : ℝ)) (beta := (274197893321051/3730550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (74611/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(327108827826943/3730550000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(274197893321051/3730550000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-43432447/625000000 : ℝ)*X 0 0+(-719141827/1250000000 : ℝ)*X 0 1+(-2870973741/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((332674057/625000000 : ℝ)*X 0 0+(-757942681/2000000000 : ℝ)*X 0 1+(-3782344199/10000000000 : ℝ)*X 0 2+(332674057/625000000 : ℝ)*X 1 0+(-757942681/2000000000 : ℝ)*X 1 1+(-3782344199/10000000000 : ℝ)*X 1 2+(332674057/625000000 : ℝ)*X 2 0+(-757942681/2000000000 : ℝ)*X 2 1+(-3782344199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-279308507/5000000000 : ℝ)*X 0 0+(-3229219327/5000000000 : ℝ)*X 0 1+(-5080122703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((316255221/625000000 : ℝ)*X 1 0+(550077271/1250000000 : ℝ)*X 1 1+(-1720592791/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((5871991821/10000000000 : ℝ)*X 2 0+(-317052881/1250000000 : ℝ)*X 2 1+(4335288539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((5554032877/10000000000 : ℝ)*X 0 0+(-3095494339/10000000000 : ℝ)*X 0 1+(-209564137/500000000 : ℝ)*X 0 2+(5554032877/10000000000 : ℝ)*X 1 0+(-3095494339/10000000000 : ℝ)*X 1 1+(-209564137/500000000 : ℝ)*X 1 2+(5554032877/10000000000 : ℝ)*X 2 0+(-3095494339/10000000000 : ℝ)*X 2 1+(-209564137/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((717/10000000000 : ℝ)*X 0 0+(-5654020407/10000000000 : ℝ)*X 0 1+(-1528668057/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((678968951/1250000000 : ℝ)*X 1 0+(1782113677/5000000000 : ℝ)*X 1 1+(-121375877/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6777608223/10000000000 : ℝ)*X 2 0+(-2787532553/10000000000 : ℝ)*X 2 1+(3037644233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((5507388139/10000000000 : ℝ)*X 0 0+(-221098111/625000000 : ℝ)*X 0 1+(-765157467/2000000000 : ℝ)*X 0 2+(5507388139/10000000000 : ℝ)*X 1 0+(-221098111/625000000 : ℝ)*X 1 1+(-765157467/2000000000 : ℝ)*X 1 2+(5507388139/10000000000 : ℝ)*X 2 0+(-221098111/625000000 : ℝ)*X 2 1+(-765157467/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((77/1250000000 : ℝ)*X 0 0+(-6123865453/10000000000 : ℝ)*X 0 1+(-5644598343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((6793277473/10000000000 : ℝ)*X 1 0+(3022414927/10000000000 : ℝ)*X 1 1+(-2782553561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((676796783/1250000000 : ℝ)*X 2 0+(-1944119587/5000000000 : ℝ)*X 2 1+(143186611/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((2755437461/5000000000 : ℝ)*X 0 0+(-76589717/200000000 : ℝ)*X 0 1+(-3529781909/10000000000 : ℝ)*X 0 2+(2755437461/5000000000 : ℝ)*X 1 0+(-76589717/200000000 : ℝ)*X 1 1+(-3529781909/10000000000 : ℝ)*X 1 2+(2755437461/5000000000 : ℝ)*X 2 0+(-76589717/200000000 : ℝ)*X 2 1+(-3529781909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((10373/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10373/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11973590504992321715598392066103/1067972724411512500000000000000000000 : ℝ) := by norm_num
    linear_combination (196621/12500000000 : ℝ)*(base1) + (569646746697/1000000000000 : ℝ)*(base39) + (254868771813/1000000000000 : ℝ)*(base50) + (7865410207/1000000000000 : ℝ)*(base60) + (69498854879/31250000000 : ℝ)*(major_s2_0) + (69498854879/31250000000 : ℝ)*(major_s2_1) + (69498854879/31250000000 : ℝ)*(major_s2_2) + (3427309/100000000000 : ℝ)*(sp_s2_6) + (93173573467/31250000000 : ℝ)*(sp_s2_7) + (2981625071623/1000000000000 : ℝ)*(sp_s2_8) + (372702776173/125000000000 : ℝ)*(sp_s2_9) + (293249580137/200000000000 : ℝ)*(sp_s2_13) + (2161259/25000000000 : ℝ)*(sp_s2_20) + (17889/6250000000 : ℝ)*(sp_s2_22) + (293259580691/200000000000 : ℝ)*(f.failure) + (2981625071623/1000000000000 : ℝ)*(f.sum) + (99357906937219030137/275765986550000000000000000000000 : ℝ)*base63 + (2941493345169127/3730550000000000000000000000 : ℝ)*base65 + (2245281604586233/1848025000000000000000000000 : ℝ)*base67 + (1258666413888711/3730550000000000000000000000 : ℝ)*base68 + (571758284794676251/8255707150000000000000000000000 : ℝ)*base71 + (18442618497061/38727500000000000000000000 : ℝ)*base73 + (1341442355592677/3696050000000000000000000000 : ℝ)*base74 + (14396666487341/22130000000000000000000000 : ℝ)*base77 + (9753636322983586903/28627755275000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (669/2500000000000000 : ℝ)*base87 + (669/2500000000000000 : ℝ)*base89 + (669/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42181/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-42181/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25614452903361563446719572928243/4271890897646050000000000000000000000 : ℝ) := by norm_num
    linear_combination (177503892371/62500000000 : ℝ)*(base39) + (66182374449/40000000000 : ℝ)*(base40) + (1961330973/100000000000 : ℝ)*(base60) + (335474482111/62500000000 : ℝ)*(major_s2_0) + (335474482111/62500000000 : ℝ)*(major_s2_1) + (335474482111/62500000000 : ℝ)*(major_s2_2) + (19983691/500000000000 : ℝ)*(sp_s2_0) + (2709089/500000000000 : ℝ)*(sp_s2_9) + (18508797/250000000000 : ℝ)*(sp_s2_13) + (3598097224169/500000000000 : ℝ)*(sp_s2_14) + (7196202906919/1000000000000 : ℝ)*(sp_s2_15) + (7196228997541/1000000000000 : ℝ)*(sp_s2_16) + (3538872977957/1000000000000 : ℝ)*(sp_s2_19) + (19693/625000000 : ℝ)*(sp_s2_21) + (442368376643/125000000000 : ℝ)*(f.failure) + (7196234415719/1000000000000 : ℝ)*(f.sum) + (90797149378434609011/275765986550000000000000000000000 : ℝ)*base62 + (1347314087207867/1865275000000000000000000000 : ℝ)*base65 + (2473901265850667/3696050000000000000000000000 : ℝ)*base67 + (95629523089037/3730550000000000000000000000 : ℝ)*base68 + (2100261440728289991/4127853575000000000000000000000 : ℝ)*base71 + (88697443934357/154910000000000000000000000 : ℝ)*base73 + (75949733369293/462006250000000000000000000 : ℝ)*base74 + (2604213816353/22130000000000000000000000 : ℝ)*base77 + (12019051158879173553/14313877637500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (363/1562500000000000 : ℝ)*base86 + (363/1562500000000000 : ℝ)*base88 + (363/1562500000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8451/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8451/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (257705460243980650361667597189/42718908976460500000000000000000000 : ℝ) := by norm_num
    linear_combination (709820012097/250000000000 : ℝ)*(base39) + (147528563871/125000000000 : ℝ)*(base40) + (4041755689/200000000000 : ℝ)*(base50) + (291297/500000000000 : ℝ)*(base59) + (2682119699813/500000000000 : ℝ)*(major_s2_0) + (2682119699813/500000000000 : ℝ)*(major_s2_1) + (2682119699813/500000000000 : ℝ)*(major_s2_2) + (58644373/1000000000000 : ℝ)*(sp_s2_7) + (10409499/500000000000 : ℝ)*(sp_s2_8) + (8902713/500000000000 : ℝ)*(sp_s2_16) + (898960171271/125000000000 : ℝ)*(sp_s2_20) + (3595859597771/500000000000 : ℝ)*(sp_s2_21) + (1438344441823/200000000000 : ℝ)*(sp_s2_22) + (707347354769/200000000000 : ℝ)*(sp_s2_25) + (707347354769/200000000000 : ℝ)*(f.failure) + (7191740014541/1000000000000 : ℝ)*(f.sum) + (10182378053719778139/275765986550000000000000000000000 : ℝ)*base63 + (356510656856177/1865275000000000000000000000 : ℝ)*base65 + (1971678588665217/3696050000000000000000000000 : ℝ)*base67 + (199058503767599/1865275000000000000000000000 : ℝ)*base69 + (5802691415959880491/16511414300000000000000000000000 : ℝ)*base70 + (223029878207943/309820000000000000000000000 : ℝ)*base73 + (1634900085966509/3696050000000000000000000000 : ℝ)*base74 + (1609528111563/44260000000000000000000000 : ℝ)*base77 + (73621934188472757419/114511021100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (471/2500000000000000 : ℝ)*base87 + (471/2500000000000000 : ℝ)*base89 + (471/2500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((15491/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15491/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-73921/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-73921/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-74611/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-74611/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10373/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10373/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42181/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-42181/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8451/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8451/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304036_s2 p hpa hpb X hX hprev1

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:01:56.541817+00:00
-- url     : https://prove2.me/submissions/5ef3e5dd-dae8-450a-b87e-376b1c674dd1

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
theorem collision_support_c311062_s1_s1_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088952627/10000000000 : ℝ)*x 0 + (253474591/500000000 : ℝ)*x 1 + (-6055508911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088952627/10000000000 : ℝ)^9 ≤ (2889606475193/50000000000000 : ℝ)^7 := by
    have hnat : (1088952627 : ℕ)^9*50000000000000^7 ≤ 2889606475193^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088952627 10000000000 2889606475193 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253474591/500000000 : ℝ)^9 ≤ (5218895026927/12500000000000 : ℝ)^7 := by
    have hnat : (253474591 : ℕ)^9*12500000000000^7 ≤ 5218895026927^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253474591 500000000 5218895026927 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6055508911/10000000000 : ℝ)^9 ≤ (52469626826247/100000000000000 : ℝ)^7 := by
    have hnat : (6055508911 : ℕ)^9*100000000000000^7 ≤ 52469626826247^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6055508911 10000000000 52469626826247 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088952627/10000000000 : ℝ), (253474591/500000000 : ℝ), (-6055508911/10000000000 : ℝ)] ![(2889606475193/50000000000000 : ℝ), (5218895026927/12500000000000 : ℝ), (52469626826247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088952627/10000000000 : ℝ)|^9 ≤ (2889606475193/50000000000000 : ℝ)^7
        have hw : |(-1088952627/10000000000 : ℝ)|=(1088952627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(253474591/500000000 : ℝ)|^9 ≤ (5218895026927/12500000000000 : ℝ)^7
        have hw : |(253474591/500000000 : ℝ)|=(253474591/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6055508911/10000000000 : ℝ)|^9 ≤ (52469626826247/100000000000000 : ℝ)^7
        have hw : |(-6055508911/10000000000 : ℝ)|=(6055508911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2553012439/5000000000 : ℝ)*x 0 + (-1103095137/10000000000 : ℝ)*x 1 + (-300601303/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2553012439/5000000000 : ℝ)^9 ≤ (42138400675089/100000000000000 : ℝ)^7 := by
    have hnat : (2553012439 : ℕ)^9*100000000000000^7 ≤ 42138400675089^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553012439 5000000000 42138400675089 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103095137/10000000000 : ℝ)^9 ≤ (1468973046673/25000000000000 : ℝ)^7 := by
    have hnat : (1103095137 : ℕ)^9*25000000000000^7 ≤ 1468973046673^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103095137 10000000000 1468973046673 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300601303/500000000 : ℝ)^9 ≤ (25992853559329/50000000000000 : ℝ)^7 := by
    have hnat : (300601303 : ℕ)^9*50000000000000^7 ≤ 25992853559329^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300601303 500000000 25992853559329 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2553012439/5000000000 : ℝ), (-1103095137/10000000000 : ℝ), (-300601303/500000000 : ℝ)] ![(42138400675089/100000000000000 : ℝ), (1468973046673/25000000000000 : ℝ), (25992853559329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2553012439/5000000000 : ℝ)|^9 ≤ (42138400675089/100000000000000 : ℝ)^7
        have hw : |(2553012439/5000000000 : ℝ)|=(2553012439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103095137/10000000000 : ℝ)|^9 ≤ (1468973046673/25000000000000 : ℝ)^7
        have hw : |(-1103095137/10000000000 : ℝ)|=(1103095137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-300601303/500000000 : ℝ)|^9 ≤ (25992853559329/50000000000000 : ℝ)^7
        have hw : |(-300601303/500000000 : ℝ)|=(300601303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5362585651/10000000000 : ℝ)*x 0 + (2718207649/5000000000 : ℝ)*x 1 + (1595517373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362585651/10000000000 : ℝ)^9 ≤ (22439986996147/50000000000000 : ℝ)^7 := by
    have hnat : (5362585651 : ℕ)^9*50000000000000^7 ≤ 22439986996147^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362585651 10000000000 22439986996147 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718207649/5000000000 : ℝ)^9 ≤ (45675957677299/100000000000000 : ℝ)^7 := by
    have hnat : (2718207649 : ℕ)^9*100000000000000^7 ≤ 45675957677299^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718207649 5000000000 45675957677299 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595517373/10000000000 : ℝ)^9 ≤ (9444068306333/100000000000000 : ℝ)^7 := by
    have hnat : (1595517373 : ℕ)^9*100000000000000^7 ≤ 9444068306333^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595517373 10000000000 9444068306333 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362585651/10000000000 : ℝ), (2718207649/5000000000 : ℝ), (1595517373/10000000000 : ℝ)] ![(22439986996147/50000000000000 : ℝ), (45675957677299/100000000000000 : ℝ), (9444068306333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362585651/10000000000 : ℝ)|^9 ≤ (22439986996147/50000000000000 : ℝ)^7
        have hw : |(5362585651/10000000000 : ℝ)|=(5362585651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718207649/5000000000 : ℝ)|^9 ≤ (45675957677299/100000000000000 : ℝ)^7
        have hw : |(2718207649/5000000000 : ℝ)|=(2718207649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1595517373/10000000000 : ℝ)|^9 ≤ (9444068306333/100000000000000 : ℝ)^7
        have hw : |(1595517373/10000000000 : ℝ)|=(1595517373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-95116791/625000000 : ℝ)*x 0 + (1368033581/5000000000 : ℝ)*x 1 + (-3881811643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95116791/625000000 : ℝ)^9 ≤ (8887316573679/100000000000000 : ℝ)^7 := by
    have hnat : (95116791 : ℕ)^9*100000000000000^7 ≤ 8887316573679^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95116791 625000000 8887316573679 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368033581/5000000000 : ℝ)^9 ≤ (18893213238653/100000000000000 : ℝ)^7 := by
    have hnat : (1368033581 : ℕ)^9*100000000000000^7 ≤ 18893213238653^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368033581 5000000000 18893213238653 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3881811643/5000000000 : ℝ)^9 ≤ (72219470172501/100000000000000 : ℝ)^7 := by
    have hnat : (3881811643 : ℕ)^9*100000000000000^7 ≤ 72219470172501^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3881811643 5000000000 72219470172501 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95116791/625000000 : ℝ), (1368033581/5000000000 : ℝ), (-3881811643/5000000000 : ℝ)] ![(8887316573679/100000000000000 : ℝ), (18893213238653/100000000000000 : ℝ), (72219470172501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95116791/625000000 : ℝ)|^9 ≤ (8887316573679/100000000000000 : ℝ)^7
        have hw : |(-95116791/625000000 : ℝ)|=(95116791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368033581/5000000000 : ℝ)|^9 ≤ (18893213238653/100000000000000 : ℝ)^7
        have hw : |(1368033581/5000000000 : ℝ)|=(1368033581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3881811643/5000000000 : ℝ)|^9 ≤ (72219470172501/100000000000000 : ℝ)^7
        have hw : |(-3881811643/5000000000 : ℝ)|=(3881811643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1633570623/5000000000 : ℝ)*x 0 + (-852509377/10000000000 : ℝ)*x 1 + (-1549854991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1633570623/5000000000 : ℝ)^9 ≤ (5933333375137/25000000000000 : ℝ)^7 := by
    have hnat : (1633570623 : ℕ)^9*25000000000000^7 ≤ 5933333375137^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633570623 5000000000 5933333375137 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (852509377/10000000000 : ℝ)^9 ≤ (2109379128731/50000000000000 : ℝ)^7 := by
    have hnat : (852509377 : ℕ)^9*50000000000000^7 ≤ 2109379128731^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852509377 10000000000 2109379128731 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1549854991/2000000000 : ℝ)^9 ≤ (72047908223391/100000000000000 : ℝ)^7 := by
    have hnat : (1549854991 : ℕ)^9*100000000000000^7 ≤ 72047908223391^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1549854991 2000000000 72047908223391 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1633570623/5000000000 : ℝ), (-852509377/10000000000 : ℝ), (-1549854991/2000000000 : ℝ)] ![(5933333375137/25000000000000 : ℝ), (2109379128731/50000000000000 : ℝ), (72047908223391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1633570623/5000000000 : ℝ)|^9 ≤ (5933333375137/25000000000000 : ℝ)^7
        have hw : |(1633570623/5000000000 : ℝ)|=(1633570623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-852509377/10000000000 : ℝ)|^9 ≤ (2109379128731/50000000000000 : ℝ)^7
        have hw : |(-852509377/10000000000 : ℝ)|=(852509377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1549854991/2000000000 : ℝ)|^9 ≤ (72047908223391/100000000000000 : ℝ)^7
        have hw : |(-1549854991/2000000000 : ℝ)|=(1549854991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (17550649/50000000 : ℝ)*x 0 + (1792846083/2500000000 : ℝ)*x 1 + (752350999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17550649/50000000 : ℝ)^9 ≤ (1041059385557/4000000000000 : ℝ)^7 := by
    have hnat : (17550649 : ℕ)^9*4000000000000^7 ≤ 1041059385557^7*50000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17550649 50000000 1041059385557 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1792846083/2500000000 : ℝ)^9 ≤ (65214881841921/100000000000000 : ℝ)^7 := by
    have hnat : (1792846083 : ℕ)^9*100000000000000^7 ≤ 65214881841921^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792846083 2500000000 65214881841921 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752350999/5000000000 : ℝ)^9 ≤ (8758633503949/100000000000000 : ℝ)^7 := by
    have hnat : (752350999 : ℕ)^9*100000000000000^7 ≤ 8758633503949^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752350999 5000000000 8758633503949 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17550649/50000000 : ℝ), (1792846083/2500000000 : ℝ), (752350999/5000000000 : ℝ)] ![(1041059385557/4000000000000 : ℝ), (65214881841921/100000000000000 : ℝ), (8758633503949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17550649/50000000 : ℝ)|^9 ≤ (1041059385557/4000000000000 : ℝ)^7
        have hw : |(17550649/50000000 : ℝ)|=(17550649/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1792846083/2500000000 : ℝ)|^9 ≤ (65214881841921/100000000000000 : ℝ)^7
        have hw : |(1792846083/2500000000 : ℝ)|=(1792846083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(752350999/5000000000 : ℝ)|^9 ≤ (8758633503949/100000000000000 : ℝ)^7
        have hw : |(752350999/5000000000 : ℝ)|=(752350999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (31292079/80000000 : ℝ)*x 0 + (7584091099/10000000000 : ℝ)*x 1 + (-11241/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31292079/80000000 : ℝ)^9 ≤ (14956893993773/50000000000000 : ℝ)^7 := by
    have hnat : (31292079 : ℕ)^9*50000000000000^7 ≤ 14956893993773^7*80000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31292079 80000000 14956893993773 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7584091099/10000000000 : ℝ)^9 ≤ (14015876520563/20000000000000 : ℝ)^7 := by
    have hnat : (7584091099 : ℕ)^9*20000000000000^7 ≤ 14015876520563^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7584091099 10000000000 14015876520563 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11241/19531250 : ℝ)^9 ≤ (27317567/400000000000 : ℝ)^7 := by
    have hnat : (11241 : ℕ)^9*400000000000^7 ≤ 27317567^7*19531250^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11241 19531250 27317567 400000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31292079/80000000 : ℝ), (7584091099/10000000000 : ℝ), (-11241/19531250 : ℝ)] ![(14956893993773/50000000000000 : ℝ), (14015876520563/20000000000000 : ℝ), (27317567/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31292079/80000000 : ℝ)|^9 ≤ (14956893993773/50000000000000 : ℝ)^7
        have hw : |(31292079/80000000 : ℝ)|=(31292079/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7584091099/10000000000 : ℝ)|^9 ≤ (14015876520563/20000000000000 : ℝ)^7
        have hw : |(7584091099/10000000000 : ℝ)|=(7584091099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11241/19531250 : ℝ)|^9 ≤ (27317567/400000000000 : ℝ)^7
        have hw : |(-11241/19531250 : ℝ)|=(11241/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-420739197/5000000000 : ℝ)*x 0 + (80254731/250000000 : ℝ)*x 1 + (-48746723/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420739197/5000000000 : ℝ)^9 ≤ (2074351709423/50000000000000 : ℝ)^7 := by
    have hnat : (420739197 : ℕ)^9*50000000000000^7 ≤ 2074351709423^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420739197 5000000000 2074351709423 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80254731/250000000 : ℝ)^9 ≤ (2900343261141/12500000000000 : ℝ)^7 := by
    have hnat : (80254731 : ℕ)^9*12500000000000^7 ≤ 2900343261141^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80254731 250000000 2900343261141 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48746723/62500000 : ℝ)^9 ≤ (290594201889/400000000000 : ℝ)^7 := by
    have hnat : (48746723 : ℕ)^9*400000000000^7 ≤ 290594201889^7*62500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48746723 62500000 290594201889 400000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420739197/5000000000 : ℝ), (80254731/250000000 : ℝ), (-48746723/62500000 : ℝ)] ![(2074351709423/50000000000000 : ℝ), (2900343261141/12500000000000 : ℝ), (290594201889/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420739197/5000000000 : ℝ)|^9 ≤ (2074351709423/50000000000000 : ℝ)^7
        have hw : |(-420739197/5000000000 : ℝ)|=(420739197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80254731/250000000 : ℝ)|^9 ≤ (2900343261141/12500000000000 : ℝ)^7
        have hw : |(80254731/250000000 : ℝ)|=(80254731/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48746723/62500000 : ℝ)|^9 ≤ (290594201889/400000000000 : ℝ)^7
        have hw : |(-48746723/62500000 : ℝ)|=(48746723/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1354784729/5000000000 : ℝ)*x 0 + (-379750707/2500000000 : ℝ)*x 1 + (-7785055861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354784729/5000000000 : ℝ)^9 ≤ (18658288298581/100000000000000 : ℝ)^7 := by
    have hnat : (1354784729 : ℕ)^9*100000000000000^7 ≤ 18658288298581^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354784729 5000000000 18658288298581 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379750707/2500000000 : ℝ)^9 ≤ (354632202007/4000000000000 : ℝ)^7 := by
    have hnat : (379750707 : ℕ)^9*4000000000000^7 ≤ 354632202007^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379750707 2500000000 354632202007 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7785055861/10000000000 : ℝ)^9 ≤ (1449518132913/2000000000000 : ℝ)^7 := by
    have hnat : (7785055861 : ℕ)^9*2000000000000^7 ≤ 1449518132913^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7785055861 10000000000 1449518132913 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354784729/5000000000 : ℝ), (-379750707/2500000000 : ℝ), (-7785055861/10000000000 : ℝ)] ![(18658288298581/100000000000000 : ℝ), (354632202007/4000000000000 : ℝ), (1449518132913/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354784729/5000000000 : ℝ)|^9 ≤ (18658288298581/100000000000000 : ℝ)^7
        have hw : |(1354784729/5000000000 : ℝ)|=(1354784729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-379750707/2500000000 : ℝ)|^9 ≤ (354632202007/4000000000000 : ℝ)^7
        have hw : |(-379750707/2500000000 : ℝ)|=(379750707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7785055861/10000000000 : ℝ)|^9 ≤ (1449518132913/2000000000000 : ℝ)^7
        have hw : |(-7785055861/10000000000 : ℝ)|=(7785055861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7043818949/10000000000 : ℝ)*x 0 + (731731329/2000000000 : ℝ)*x 1 + (1513150901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7043818949/10000000000 : ℝ)^9 ≤ (3982949738737/6250000000000 : ℝ)^7 := by
    have hnat : (7043818949 : ℕ)^9*6250000000000^7 ≤ 3982949738737^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7043818949 10000000000 3982949738737 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (731731329/2000000000 : ℝ)^9 ≤ (27450888914657/100000000000000 : ℝ)^7 := by
    have hnat : (731731329 : ℕ)^9*100000000000000^7 ≤ 27450888914657^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731731329 2000000000 27450888914657 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1513150901/10000000000 : ℝ)^9 ≤ (2205478810999/25000000000000 : ℝ)^7 := by
    have hnat : (1513150901 : ℕ)^9*25000000000000^7 ≤ 2205478810999^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513150901 10000000000 2205478810999 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7043818949/10000000000 : ℝ), (731731329/2000000000 : ℝ), (1513150901/10000000000 : ℝ)] ![(3982949738737/6250000000000 : ℝ), (27450888914657/100000000000000 : ℝ), (2205478810999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7043818949/10000000000 : ℝ)|^9 ≤ (3982949738737/6250000000000 : ℝ)^7
        have hw : |(7043818949/10000000000 : ℝ)|=(7043818949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(731731329/2000000000 : ℝ)|^9 ≤ (27450888914657/100000000000000 : ℝ)^7
        have hw : |(731731329/2000000000 : ℝ)|=(731731329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1513150901/10000000000 : ℝ)|^9 ≤ (2205478810999/25000000000000 : ℝ)^7
        have hw : |(1513150901/10000000000 : ℝ)|=(1513150901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7770320929/10000000000 : ℝ)*x 0 + (368355389/1000000000 : ℝ)*x 1 + (-7205497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7770320929/10000000000 : ℝ)^9 ≤ (72299584431009/100000000000000 : ℝ)^7 := by
    have hnat : (7770320929 : ℕ)^9*100000000000000^7 ≤ 72299584431009^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7770320929 10000000000 72299584431009 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (368355389/1000000000 : ℝ)^9 ≤ (27691298529099/100000000000000 : ℝ)^7 := by
    have hnat : (368355389 : ℕ)^9*100000000000000^7 ≤ 27691298529099^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368355389 1000000000 27691298529099 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7205497/10000000000 : ℝ)^9 ≤ (9117035363/100000000000000 : ℝ)^7 := by
    have hnat : (7205497 : ℕ)^9*100000000000000^7 ≤ 9117035363^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7205497 10000000000 9117035363 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7770320929/10000000000 : ℝ), (368355389/1000000000 : ℝ), (-7205497/10000000000 : ℝ)] ![(72299584431009/100000000000000 : ℝ), (27691298529099/100000000000000 : ℝ), (9117035363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7770320929/10000000000 : ℝ)|^9 ≤ (72299584431009/100000000000000 : ℝ)^7
        have hw : |(7770320929/10000000000 : ℝ)|=(7770320929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(368355389/1000000000 : ℝ)|^9 ≤ (27691298529099/100000000000000 : ℝ)^7
        have hw : |(368355389/1000000000 : ℝ)|=(368355389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7205497/10000000000 : ℝ)|^9 ≤ (9117035363/100000000000000 : ℝ)^7
        have hw : |(-7205497/10000000000 : ℝ)|=(7205497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-46781631/2500000000 : ℝ)*x 0 + (3251832917/5000000000 : ℝ)*x 1 + (-5082165167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46781631/2500000000 : ℝ)^9 ≤ (150106585067/25000000000000 : ℝ)^7 := by
    have hnat : (46781631 : ℕ)^9*25000000000000^7 ≤ 150106585067^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46781631 2500000000 150106585067 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3251832917/5000000000 : ℝ)^9 ≤ (14378542358049/25000000000000 : ℝ)^7 := by
    have hnat : (3251832917 : ℕ)^9*25000000000000^7 ≤ 14378542358049^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3251832917 5000000000 14378542358049 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5082165167/10000000000 : ℝ)^9 ≤ (41885404219727/100000000000000 : ℝ)^7 := by
    have hnat : (5082165167 : ℕ)^9*100000000000000^7 ≤ 41885404219727^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082165167 10000000000 41885404219727 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46781631/2500000000 : ℝ), (3251832917/5000000000 : ℝ), (-5082165167/10000000000 : ℝ)] ![(150106585067/25000000000000 : ℝ), (14378542358049/25000000000000 : ℝ), (41885404219727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46781631/2500000000 : ℝ)|^9 ≤ (150106585067/25000000000000 : ℝ)^7
        have hw : |(-46781631/2500000000 : ℝ)|=(46781631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3251832917/5000000000 : ℝ)|^9 ≤ (14378542358049/25000000000000 : ℝ)^7
        have hw : |(3251832917/5000000000 : ℝ)|=(3251832917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5082165167/10000000000 : ℝ)|^9 ≤ (41885404219727/100000000000000 : ℝ)^7
        have hw : |(-5082165167/10000000000 : ℝ)|=(5082165167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3454109043/5000000000 : ℝ)*x 0 + (-566034373/10000000000 : ℝ)*x 1 + (-2227180477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3454109043/5000000000 : ℝ)^9 ≤ (3884638762413/6250000000000 : ℝ)^7 := by
    have hnat : (3454109043 : ℕ)^9*6250000000000^7 ≤ 3884638762413^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3454109043 5000000000 3884638762413 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566034373/10000000000 : ℝ)^9 ≤ (38934285019/1562500000000 : ℝ)^7 := by
    have hnat : (566034373 : ℕ)^9*1562500000000^7 ≤ 38934285019^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566034373 10000000000 38934285019 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2227180477/5000000000 : ℝ)^9 ≤ (1104812048267/3125000000000 : ℝ)^7 := by
    have hnat : (2227180477 : ℕ)^9*3125000000000^7 ≤ 1104812048267^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227180477 5000000000 1104812048267 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3454109043/5000000000 : ℝ), (-566034373/10000000000 : ℝ), (-2227180477/5000000000 : ℝ)] ![(3884638762413/6250000000000 : ℝ), (38934285019/1562500000000 : ℝ), (1104812048267/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3454109043/5000000000 : ℝ)|^9 ≤ (3884638762413/6250000000000 : ℝ)^7
        have hw : |(3454109043/5000000000 : ℝ)|=(3454109043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-566034373/10000000000 : ℝ)|^9 ≤ (38934285019/1562500000000 : ℝ)^7
        have hw : |(-566034373/10000000000 : ℝ)|=(566034373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2227180477/5000000000 : ℝ)|^9 ≤ (1104812048267/3125000000000 : ℝ)^7
        have hw : |(-2227180477/5000000000 : ℝ)|=(2227180477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3304424943/10000000000 : ℝ)*x 0 + (432744873/625000000 : ℝ)*x 1 + (132287309/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3304424943/10000000000 : ℝ)^9 ≤ (752566253099/3125000000000 : ℝ)^7 := by
    have hnat : (3304424943 : ℕ)^9*3125000000000^7 ≤ 752566253099^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3304424943 10000000000 752566253099 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432744873/625000000 : ℝ)^9 ≤ (3116794575277/5000000000000 : ℝ)^7 := by
    have hnat : (432744873 : ℕ)^9*5000000000000^7 ≤ 3116794575277^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432744873 625000000 3116794575277 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132287309/625000000 : ℝ)^9 ≤ (13581988383111/100000000000000 : ℝ)^7 := by
    have hnat : (132287309 : ℕ)^9*100000000000000^7 ≤ 13581988383111^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132287309 625000000 13581988383111 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3304424943/10000000000 : ℝ), (432744873/625000000 : ℝ), (132287309/625000000 : ℝ)] ![(752566253099/3125000000000 : ℝ), (3116794575277/5000000000000 : ℝ), (13581988383111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3304424943/10000000000 : ℝ)|^9 ≤ (752566253099/3125000000000 : ℝ)^7
        have hw : |(3304424943/10000000000 : ℝ)|=(3304424943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(432744873/625000000 : ℝ)|^9 ≤ (3116794575277/5000000000000 : ℝ)^7
        have hw : |(432744873/625000000 : ℝ)|=(432744873/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132287309/625000000 : ℝ)|^9 ≤ (13581988383111/100000000000000 : ℝ)^7
        have hw : |(132287309/625000000 : ℝ)|=(132287309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s1_s1_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (8277536731/10000000000 : ℝ)*x 0 + (598332193/2000000000 : ℝ)*x 1 + (-132386679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8277536731/10000000000 : ℝ)^9 ≤ (78423151851013/100000000000000 : ℝ)^7 := by
    have hnat : (8277536731 : ℕ)^9*100000000000000^7 ≤ 78423151851013^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8277536731 10000000000 78423151851013 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598332193/2000000000 : ℝ)^9 ≤ (10596027034783/50000000000000 : ℝ)^7 := by
    have hnat : (598332193 : ℕ)^9*50000000000000^7 ≤ 10596027034783^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598332193 2000000000 10596027034783 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132386679/10000000000 : ℝ)^9 ≤ (15391762779/4000000000000 : ℝ)^7 := by
    have hnat : (132386679 : ℕ)^9*4000000000000^7 ≤ 15391762779^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132386679 10000000000 15391762779 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8277536731/10000000000 : ℝ), (598332193/2000000000 : ℝ), (-132386679/10000000000 : ℝ)] ![(78423151851013/100000000000000 : ℝ), (10596027034783/50000000000000 : ℝ), (15391762779/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8277536731/10000000000 : ℝ)|^9 ≤ (78423151851013/100000000000000 : ℝ)^7
        have hw : |(8277536731/10000000000 : ℝ)|=(8277536731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598332193/2000000000 : ℝ)|^9 ≤ (10596027034783/50000000000000 : ℝ)^7
        have hw : |(598332193/2000000000 : ℝ)|=(598332193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-132386679/10000000000 : ℝ)|^9 ≤ (15391762779/4000000000000 : ℝ)^7
        have hw : |(-132386679/10000000000 : ℝ)|=(132386679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311062_s1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((4357/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4357/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21571/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21571/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37809/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37809/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((70071/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70071/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35009/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35009/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13741/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13741/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (89829/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (4357/5000 : ℝ) ^ (71/16 : ℝ) ≤ (678618064187534937/1250000000000000000 : ℝ) := by
    have hpowers : (4357/5000 : ℝ)^71 ≤ (678618064187534937/1250000000000000000 : ℝ)^16 := by
      have hnat : (4357 : ℕ)^71*1250000000000000000^16 ≤ 678618064187534937^16*5000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4357 5000 678618064187534937 1250000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4357/5000 : ℝ)) (X := (678618064187534937/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (1928618064187534937/1250000000000000000 : ℝ) ≤ (11026608734324609/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (1928618064187534937/1250000000000000000 : ℝ)^16 ≤ (11026608734324609/10000000000000000 : ℝ)^71 := by
      have hnat : (1928618064187534937 : ℕ)^16*10000000000000000^71 ≤ 11026608734324609^71*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1928618064187534937 1250000000000000000 11026608734324609 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11026608734324609/10000000000000000 : ℝ)) (X := (1928618064187534937/1250000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1303618064187534937/625000000000000000 : ℝ) ≤ (5900899971257529/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (1303618064187534937/625000000000000000 : ℝ)^16 ≤ (5900899971257529/5000000000000000 : ℝ)^71 := by
      have hnat : (1303618064187534937 : ℕ)^16*5000000000000000^71 ≤ 5900899971257529^71*625000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1303618064187534937 625000000000000000 5900899971257529 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5900899971257529/5000000000000000 : ℝ)) (X := (1303618064187534937/625000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1026608734324609/8714000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(775191208190449/8714000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (4357/5000 : ℝ)) (alpha := (1026608734324609/8714000000000000 : ℝ)) (beta := (775191208190449/8714000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4357/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1026608734324609/8714000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(775191208190449/8714000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (21571/25000 : ℝ) ^ (71/16 : ℝ) ≤ (51962564166583181233/100000000000000000000 : ℝ) := by
    have hpowers : (21571/25000 : ℝ)^71 ≤ (51962564166583181233/100000000000000000000 : ℝ)^16 := by
      have hnat : (21571 : ℕ)^71*100000000000000000000^16 ≤ 51962564166583181233^16*25000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21571 25000 51962564166583181233 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21571/25000 : ℝ)) (X := (51962564166583181233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (151962564166583181233/100000000000000000000 : ℝ) ≤ (10988912864682877/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (151962564166583181233/100000000000000000000 : ℝ)^16 ≤ (10988912864682877/10000000000000000 : ℝ)^71 := by
      have hnat : (151962564166583181233 : ℕ)^16*10000000000000000^71 ≤ 10988912864682877^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        151962564166583181233 100000000000000000000 10988912864682877 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10988912864682877/10000000000000000 : ℝ)) (X := (151962564166583181233/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (101962564166583181233/50000000000000000000 : ℝ) ≤ (11741940789083019/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (101962564166583181233/50000000000000000000 : ℝ)^16 ≤ (11741940789083019/10000000000000000 : ℝ)^71 := by
      have hnat : (101962564166583181233 : ℕ)^16*10000000000000000^71 ≤ 11741940789083019^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101962564166583181233 50000000000000000000 11741940789083019 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11741940789083019/10000000000000000 : ℝ)) (X := (101962564166583181233/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(988912864682877/8628400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(376513962200071/4314200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (21571/25000 : ℝ)) (alpha := (988912864682877/8628400000000000 : ℝ)) (beta := (376513962200071/4314200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (21571/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(988912864682877/8628400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(376513962200071/4314200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (37809/50000 : ℝ) ^ (71/16 : ℝ) ≤ (28933386315027596239/100000000000000000000 : ℝ) := by
    have hpowers : (37809/50000 : ℝ)^71 ≤ (28933386315027596239/100000000000000000000 : ℝ)^16 := by
      have hnat : (37809 : ℕ)^71*100000000000000000000^16 ≤ 28933386315027596239^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37809 50000 28933386315027596239 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37809/50000 : ℝ)) (X := (28933386315027596239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (128933386315027596239/100000000000000000000 : ℝ) ≤ (5294696587859169/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (128933386315027596239/100000000000000000000 : ℝ)^16 ≤ (5294696587859169/5000000000000000 : ℝ)^71 := by
      have hnat : (128933386315027596239 : ℕ)^16*5000000000000000^71 ≤ 5294696587859169^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        128933386315027596239 100000000000000000000 5294696587859169 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5294696587859169/5000000000000000 : ℝ)) (X := (128933386315027596239/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (78933386315027596239/50000000000000000000 : ℝ) ≤ (11083712064473441/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (78933386315027596239/50000000000000000000 : ℝ)^16 ≤ (11083712064473441/10000000000000000 : ℝ)^71 := by
      have hnat : (78933386315027596239 : ℕ)^16*10000000000000000^71 ≤ 11083712064473441^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78933386315027596239 50000000000000000000 11083712064473441 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11083712064473441/10000000000000000 : ℝ)) (X := (78933386315027596239/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(294696587859169/3780900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(494318888755103/7561800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (37809/50000 : ℝ)) (alpha := (294696587859169/3780900000000000 : ℝ)) (beta := (494318888755103/7561800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (37809/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(294696587859169/3780900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(494318888755103/7561800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1088952627/10000000000 : ℝ)*X 0 0+(253474591/500000000 : ℝ)*X 0 1+(-6055508911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2553012439/5000000000 : ℝ)*X 1 0+(-1103095137/10000000000 : ℝ)*X 1 1+(-300601303/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5362585651/10000000000 : ℝ)*X 2 0+(2718207649/5000000000 : ℝ)*X 2 1+(1595517373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-95116791/625000000 : ℝ)*X 0 0+(1368033581/5000000000 : ℝ)*X 0 1+(-3881811643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1633570623/5000000000 : ℝ)*X 1 0+(-852509377/10000000000 : ℝ)*X 1 1+(-1549854991/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((17550649/50000000 : ℝ)*X 2 0+(1792846083/2500000000 : ℝ)*X 2 1+(752350999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((31292079/80000000 : ℝ)*X 0 0+(7584091099/10000000000 : ℝ)*X 0 1+(-11241/19531250 : ℝ)*X 0 2+(31292079/80000000 : ℝ)*X 1 0+(7584091099/10000000000 : ℝ)*X 1 1+(-11241/19531250 : ℝ)*X 1 2+(31292079/80000000 : ℝ)*X 2 0+(7584091099/10000000000 : ℝ)*X 2 1+(-11241/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-420739197/5000000000 : ℝ)*X 0 0+(80254731/250000000 : ℝ)*X 0 1+(-48746723/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1354784729/5000000000 : ℝ)*X 1 0+(-379750707/2500000000 : ℝ)*X 1 1+(-7785055861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7043818949/10000000000 : ℝ)*X 2 0+(731731329/2000000000 : ℝ)*X 2 1+(1513150901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7770320929/10000000000 : ℝ)*X 0 0+(368355389/1000000000 : ℝ)*X 0 1+(-7205497/10000000000 : ℝ)*X 0 2+(7770320929/10000000000 : ℝ)*X 1 0+(368355389/1000000000 : ℝ)*X 1 1+(-7205497/10000000000 : ℝ)*X 1 2+(7770320929/10000000000 : ℝ)*X 2 0+(368355389/1000000000 : ℝ)*X 2 1+(-7205497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-46781631/2500000000 : ℝ)*X 0 0+(3251832917/5000000000 : ℝ)*X 0 1+(-5082165167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3454109043/5000000000 : ℝ)*X 1 0+(-566034373/10000000000 : ℝ)*X 1 1+(-2227180477/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3304424943/10000000000 : ℝ)*X 2 0+(432744873/625000000 : ℝ)*X 2 1+(132287309/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8277536731/10000000000 : ℝ)*X 0 0+(598332193/2000000000 : ℝ)*X 0 1+(-132386679/10000000000 : ℝ)*X 0 2+(8277536731/10000000000 : ℝ)*X 1 0+(598332193/2000000000 : ℝ)*X 1 1+(-132386679/10000000000 : ℝ)*X 1 2+(8277536731/10000000000 : ℝ)*X 2 0+(598332193/2000000000 : ℝ)*X 2 1+(-132386679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((70071/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70071/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1646708582595624786159044700773/296122756685250000000000000000000000 : ℝ) := by norm_num
    linear_combination (392678187437/500000000000 : ℝ)*(base7) + (187991/1000000000000 : ℝ)*(base39) + (525011/500000000000 : ℝ)*(base49) + (17628775723/1000000000000 : ℝ)*(base60) + (542822658427/250000000000 : ℝ)*(major_s1_0) + (542822658427/250000000000 : ℝ)*(major_s1_1) + (542822658427/250000000000 : ℝ)*(major_s1_2) + (2092337/250000000000 : ℝ)*(sp_s1_0) + (6083481/1000000000000 : ℝ)*(sp_s1_1) + (63776636147/25000000000 : ℝ)*(sp_s1_7) + (2551100533093/1000000000000 : ℝ)*(sp_s1_8) + (1275553308287/500000000000 : ℝ)*(sp_s1_9) + (1053255326711/500000000000 : ℝ)*(sp_s1_13) + (16400673/500000000000 : ℝ)*(sp_s1_14) + (330288569637/250000000000 : ℝ)*(f.failure) + (1275553308287/500000000000 : ℝ)*(f.sum) + (43953091959060946697/81557793900000000000000000000000 : ℝ)*base62 + (279398082297229/1890450000000000000000000000 : ℝ)*base64 + (573338971074577/1078550000000000000000000000 : ℝ)*base67 + (452780496289/461535644531250000000000 : ℝ)*base68 + (28411770293879894957/82366906500000000000000000000000 : ℝ)*base71 + (902058920530873/2178500000000000000000000000 : ℝ)*base73 + (1066721816785021/2157100000000000000000000000 : ℝ)*base74 + (1308829008696057/2178500000000000000000000000 : ℝ)*base76 + (684732799677664723/46992423500000000000000000000000 : ℝ)*base79 + (419/6250000000000000 : ℝ)*base87 + (419/6250000000000000 : ℝ)*base89 + (419/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35009/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35009/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1637008228325371722040361835931/118449102674100000000000000000000000 : ℝ) := by norm_num
    linear_combination (157835886663/200000000000 : ℝ)*(base7) + (275051/1000000000000 : ℝ)*(base40) + (97161/200000000000 : ℝ)*(base59) + (1063492043887/500000000000 : ℝ)*(major_s1_0) + (1063492043887/500000000000 : ℝ)*(major_s1_1) + (1063492043887/500000000000 : ℝ)*(major_s1_2) + (32783/8000000000 : ℝ)*(sp_s1_0) + (1291089/500000000000 : ℝ)*(sp_s1_2) + (43771187/500000000000 : ℝ)*(sp_s1_8) + (1243578088901/500000000000 : ℝ)*(sp_s1_14) + (2487072733303/1000000000000 : ℝ)*(sp_s1_15) + (2487157693499/1000000000000 : ℝ)*(sp_s1_16) + (2083346807989/1000000000000 : ℝ)*(sp_s1_20) + (27922971/1000000000000 : ℝ)*(sp_s1_27) + (258839059529/200000000000 : ℝ)*(f.failure) + (2487160275677/1000000000000 : ℝ)*(f.sum) + (4665832306015580923/163115587800000000000000000000000 : ℝ)*base63 + (2276233945866911/3780900000000000000000000000 : ℝ)*base65 + (1135157252966853/2157100000000000000000000000 : ℝ)*base66 + (913618552278703/1890450000000000000000000000 : ℝ)*base69 + (106229815120819146917/164733813000000000000000000000000 : ℝ)*base71 + (4380876737813237/4357000000000000000000000000 : ℝ)*base72 + (2589102076877279/4314200000000000000000000000 : ℝ)*base75 + (3990970743288383/4357000000000000000000000000 : ℝ)*base77 + (35487881074297613637/93984847000000000000000000000000 : ℝ)*base78 + (1977/5000000000000000 : ℝ)*base86 + (1977/5000000000000000 : ℝ)*base88 + (1977/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13741/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13741/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (439243542418268769772927338997/32013270993000000000000000000000000 : ℝ) := by norm_num
    linear_combination (493334274947/1000000000000 : ℝ)*(base7) + (21813541/1000000000000 : ℝ)*(base11) + (39399683037/250000000000 : ℝ)*(base39) + (2056076603299/1000000000000 : ℝ)*(major_s1_0) + (2056076603299/1000000000000 : ℝ)*(major_s1_1) + (2056076603299/1000000000000 : ℝ)*(major_s1_2) + (34578453/1000000000000 : ℝ)*(sp_s1_0) + (1333069/1000000000000 : ℝ)*(sp_s1_2) + (4766971/40000000000 : ℝ)*(sp_s1_9) + (1778139/250000000000 : ℝ)*(sp_s1_20) + (2565603499531/1000000000000 : ℝ)*(sp_s1_21) + (102626395661/40000000000 : ℝ)*(sp_s1_22) + (128276969209/50000000000 : ℝ)*(sp_s1_23) + (1744377740007/1000000000000 : ℝ)*(sp_s1_27) + (250210115523/200000000000 : ℝ)*(f.failure) + (102626395661/40000000000 : ℝ)*(f.sum) + (4666450956287087777/8817058800000000000000000000000 : ℝ)*base62 + (1059480618942823/7561800000000000000000000000 : ℝ)*base64 + (21618129238483/116600000000000000000000000 : ℝ)*base66 + (1477650099450659/3780900000000000000000000000 : ℝ)*base68 + (65884861847511591091/329467626000000000000000000000000 : ℝ)*base70 + (5086844060149749/8714000000000000000000000000 : ℝ)*base72 + (14903167959979/233200000000000000000000000 : ℝ)*base75 + (4890145969319291/8714000000000000000000000000 : ℝ)*base77 + (1311156585560140377/5080262000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (1499/5000000000000000 : ℝ)*base86 + (1499/5000000000000000 : ℝ)*base88 + (1499/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((4357/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4357/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21571/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21571/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37809/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37809/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((70071/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70071/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35009/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35009/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13741/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13741/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311062_s1 p hpa hpb X hX hprev0

#print axioms solution

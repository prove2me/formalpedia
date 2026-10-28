-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302053_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:29.897192+00:00
-- url     : https://prove2.me/submissions/4a4a68e7-54b1-429c-982d-f5e546a40bf1

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
theorem collision_support_c302053_s6_s6_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2404048003/10000000000 : ℝ)*x 0 + (2600119757/5000000000 : ℝ)*x 1 + (1309302393/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2404048003/10000000000 : ℝ)^33 ≤ (15235086996119/100000000000000 : ℝ)^25 := by
    have hnat : (2404048003 : ℕ)^33*100000000000000^25 ≤ 15235086996119^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404048003 10000000000 15235086996119 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2600119757/5000000000 : ℝ)^33 ≤ (42184297191151/100000000000000 : ℝ)^25 := by
    have hnat : (2600119757 : ℕ)^33*100000000000000^25 ≤ 42184297191151^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600119757 5000000000 42184297191151 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309302393/2500000000 : ℝ)^33 ≤ (42580615800461/100000000000000 : ℝ)^25 := by
    have hnat : (1309302393 : ℕ)^33*100000000000000^25 ≤ 42580615800461^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309302393 2500000000 42580615800461 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2404048003/10000000000 : ℝ), (2600119757/5000000000 : ℝ), (1309302393/2500000000 : ℝ)] ![(15235086996119/100000000000000 : ℝ), (42184297191151/100000000000000 : ℝ), (42580615800461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2404048003/10000000000 : ℝ)|^33 ≤ (15235086996119/100000000000000 : ℝ)^25
        have hw : |(-2404048003/10000000000 : ℝ)|=(2404048003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2600119757/5000000000 : ℝ)|^33 ≤ (42184297191151/100000000000000 : ℝ)^25
        have hw : |(2600119757/5000000000 : ℝ)|=(2600119757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309302393/2500000000 : ℝ)|^33 ≤ (42580615800461/100000000000000 : ℝ)^25
        have hw : |(1309302393/2500000000 : ℝ)|=(1309302393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4586981983/10000000000 : ℝ)*x 0 + (772444413/1250000000 : ℝ)*x 1 + (-38291983/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4586981983/10000000000 : ℝ)^33 ≤ (35745031593969/100000000000000 : ℝ)^25 := by
    have hnat : (4586981983 : ℕ)^33*100000000000000^25 ≤ 35745031593969^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4586981983 10000000000 35745031593969 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772444413/1250000000 : ℝ)^33 ≤ (10594818725257/20000000000000 : ℝ)^25 := by
    have hnat : (772444413 : ℕ)^33*20000000000000^25 ≤ 10594818725257^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772444413 1250000000 10594818725257 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38291983/200000000 : ℝ)^33 ≤ (11280874755081/100000000000000 : ℝ)^25 := by
    have hnat : (38291983 : ℕ)^33*100000000000000^25 ≤ 11280874755081^25*200000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38291983 200000000 11280874755081 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4586981983/10000000000 : ℝ), (772444413/1250000000 : ℝ), (-38291983/200000000 : ℝ)] ![(35745031593969/100000000000000 : ℝ), (10594818725257/20000000000000 : ℝ), (11280874755081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4586981983/10000000000 : ℝ)|^33 ≤ (35745031593969/100000000000000 : ℝ)^25
        have hw : |(4586981983/10000000000 : ℝ)|=(4586981983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772444413/1250000000 : ℝ)|^33 ≤ (10594818725257/20000000000000 : ℝ)^25
        have hw : |(772444413/1250000000 : ℝ)|=(772444413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38291983/200000000 : ℝ)|^33 ≤ (11280874755081/100000000000000 : ℝ)^25
        have hw : |(-38291983/200000000 : ℝ)|=(38291983/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6619094381/10000000000 : ℝ)*x 0 + (386238687/1250000000 : ℝ)*x 1 + (1520521973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6619094381/10000000000 : ℝ)^33 ≤ (14500872231267/25000000000000 : ℝ)^25 := by
    have hnat : (6619094381 : ℕ)^33*25000000000000^25 ≤ 14500872231267^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6619094381 10000000000 14500872231267 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386238687/1250000000 : ℝ)^33 ≤ (21219170475099/100000000000000 : ℝ)^25 := by
    have hnat : (386238687 : ℕ)^33*100000000000000^25 ≤ 21219170475099^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386238687 1250000000 21219170475099 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1520521973/5000000000 : ℝ)^33 ≤ (20777340588811/100000000000000 : ℝ)^25 := by
    have hnat : (1520521973 : ℕ)^33*100000000000000^25 ≤ 20777340588811^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1520521973 5000000000 20777340588811 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6619094381/10000000000 : ℝ), (386238687/1250000000 : ℝ), (1520521973/5000000000 : ℝ)] ![(14500872231267/25000000000000 : ℝ), (21219170475099/100000000000000 : ℝ), (20777340588811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6619094381/10000000000 : ℝ)|^33 ≤ (14500872231267/25000000000000 : ℝ)^25
        have hw : |(6619094381/10000000000 : ℝ)|=(6619094381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386238687/1250000000 : ℝ)|^33 ≤ (21219170475099/100000000000000 : ℝ)^25
        have hw : |(386238687/1250000000 : ℝ)|=(386238687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1520521973/5000000000 : ℝ)|^33 ≤ (20777340588811/100000000000000 : ℝ)^25
        have hw : |(1520521973/5000000000 : ℝ)|=(1520521973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-453418291/2000000000 : ℝ)*x 0 + (1031149481/2500000000 : ℝ)*x 1 + (6343115949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453418291/2000000000 : ℝ)^33 ≤ (14100000654923/100000000000000 : ℝ)^25 := by
    have hnat : (453418291 : ℕ)^33*100000000000000^25 ≤ 14100000654923^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453418291 2000000000 14100000654923 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031149481/2500000000 : ℝ)^33 ≤ (31067316145107/100000000000000 : ℝ)^25 := by
    have hnat : (1031149481 : ℕ)^33*100000000000000^25 ≤ 31067316145107^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031149481 2500000000 31067316145107 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6343115949/10000000000 : ℝ)^33 ≤ (54832683187237/100000000000000 : ℝ)^25 := by
    have hnat : (6343115949 : ℕ)^33*100000000000000^25 ≤ 54832683187237^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6343115949 10000000000 54832683187237 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453418291/2000000000 : ℝ), (1031149481/2500000000 : ℝ), (6343115949/10000000000 : ℝ)] ![(14100000654923/100000000000000 : ℝ), (31067316145107/100000000000000 : ℝ), (54832683187237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453418291/2000000000 : ℝ)|^33 ≤ (14100000654923/100000000000000 : ℝ)^25
        have hw : |(-453418291/2000000000 : ℝ)|=(453418291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031149481/2500000000 : ℝ)|^33 ≤ (31067316145107/100000000000000 : ℝ)^25
        have hw : |(1031149481/2500000000 : ℝ)|=(1031149481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6343115949/10000000000 : ℝ)|^33 ≤ (54832683187237/100000000000000 : ℝ)^25
        have hw : |(6343115949/10000000000 : ℝ)|=(6343115949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4063170851/10000000000 : ℝ)*x 0 + (-80555427/625000000 : ℝ)*x 1 + (3517034447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4063170851/10000000000 : ℝ)^33 ≤ (761450927209/2500000000000 : ℝ)^25 := by
    have hnat : (4063170851 : ℕ)^33*2500000000000^25 ≤ 761450927209^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4063170851 10000000000 761450927209 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80555427/625000000 : ℝ)^33 ≤ (6690884275607/100000000000000 : ℝ)^25 := by
    have hnat : (80555427 : ℕ)^33*100000000000000^25 ≤ 6690884275607^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80555427 625000000 6690884275607 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3517034447/5000000000 : ℝ)^33 ≤ (62851078623891/100000000000000 : ℝ)^25 := by
    have hnat : (3517034447 : ℕ)^33*100000000000000^25 ≤ 62851078623891^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3517034447 5000000000 62851078623891 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4063170851/10000000000 : ℝ), (-80555427/625000000 : ℝ), (3517034447/5000000000 : ℝ)] ![(761450927209/2500000000000 : ℝ), (6690884275607/100000000000000 : ℝ), (62851078623891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4063170851/10000000000 : ℝ)|^33 ≤ (761450927209/2500000000000 : ℝ)^25
        have hw : |(4063170851/10000000000 : ℝ)|=(4063170851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80555427/625000000 : ℝ)|^33 ≤ (6690884275607/100000000000000 : ℝ)^25
        have hw : |(-80555427/625000000 : ℝ)|=(80555427/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3517034447/5000000000 : ℝ)|^33 ≤ (62851078623891/100000000000000 : ℝ)^25
        have hw : |(3517034447/5000000000 : ℝ)|=(3517034447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2042445317/5000000000 : ℝ)*x 0 + (45181153/62500000 : ℝ)*x 1 + (-180061053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042445317/5000000000 : ℝ)^33 ≤ (30673135437797/100000000000000 : ℝ)^25 := by
    have hnat : (2042445317 : ℕ)^33*100000000000000^25 ≤ 30673135437797^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042445317 5000000000 30673135437797 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45181153/62500000 : ℝ)^33 ≤ (16290035643929/25000000000000 : ℝ)^25 := by
    have hnat : (45181153 : ℕ)^33*25000000000000^25 ≤ 16290035643929^25*62500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45181153 62500000 16290035643929 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180061053/2000000000 : ℝ)^33 ≤ (2083360985631/50000000000000 : ℝ)^25 := by
    have hnat : (180061053 : ℕ)^33*50000000000000^25 ≤ 2083360985631^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180061053 2000000000 2083360985631 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2042445317/5000000000 : ℝ), (45181153/62500000 : ℝ), (-180061053/2000000000 : ℝ)] ![(30673135437797/100000000000000 : ℝ), (16290035643929/25000000000000 : ℝ), (2083360985631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2042445317/5000000000 : ℝ)|^33 ≤ (30673135437797/100000000000000 : ℝ)^25
        have hw : |(2042445317/5000000000 : ℝ)|=(2042445317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45181153/62500000 : ℝ)|^33 ≤ (16290035643929/25000000000000 : ℝ)^25
        have hw : |(45181153/62500000 : ℝ)|=(45181153/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-180061053/2000000000 : ℝ)|^33 ≤ (2083360985631/50000000000000 : ℝ)^25
        have hw : |(-180061053/2000000000 : ℝ)|=(180061053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6286375247/10000000000 : ℝ)*x 0 + (2379464633/5000000000 : ℝ)*x 1 + (758012033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6286375247/10000000000 : ℝ)^33 ≤ (27093081423559/50000000000000 : ℝ)^25 := by
    have hnat : (6286375247 : ℕ)^33*50000000000000^25 ≤ 27093081423559^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6286375247 10000000000 27093081423559 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2379464633/5000000000 : ℝ)^33 ≤ (3752426632443/10000000000000 : ℝ)^25 := by
    have hnat : (2379464633 : ℕ)^33*10000000000000^25 ≤ 3752426632443^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2379464633 5000000000 3752426632443 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (758012033/5000000000 : ℝ)^33 ≤ (8289570818061/100000000000000 : ℝ)^25 := by
    have hnat : (758012033 : ℕ)^33*100000000000000^25 ≤ 8289570818061^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758012033 5000000000 8289570818061 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6286375247/10000000000 : ℝ), (2379464633/5000000000 : ℝ), (758012033/5000000000 : ℝ)] ![(27093081423559/50000000000000 : ℝ), (3752426632443/10000000000000 : ℝ), (8289570818061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6286375247/10000000000 : ℝ)|^33 ≤ (27093081423559/50000000000000 : ℝ)^25
        have hw : |(6286375247/10000000000 : ℝ)|=(6286375247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2379464633/5000000000 : ℝ)|^33 ≤ (3752426632443/10000000000000 : ℝ)^25
        have hw : |(2379464633/5000000000 : ℝ)|=(2379464633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(758012033/5000000000 : ℝ)|^33 ≤ (8289570818061/100000000000000 : ℝ)^25
        have hw : |(758012033/5000000000 : ℝ)|=(758012033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1237403767/10000000000 : ℝ)*x 0 + (2453241283/5000000000 : ℝ)*x 1 + (1580503447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1237403767/10000000000 : ℝ)^33 ≤ (1585094289177/25000000000000 : ℝ)^25 := by
    have hnat : (1237403767 : ℕ)^33*25000000000000^25 ≤ 1585094289177^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237403767 10000000000 1585094289177 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2453241283/5000000000 : ℝ)^33 ≤ (19533800483773/50000000000000 : ℝ)^25 := by
    have hnat : (2453241283 : ℕ)^33*50000000000000^25 ≤ 19533800483773^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453241283 5000000000 19533800483773 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1580503447/2500000000 : ℝ)^33 ≤ (54592021860391/100000000000000 : ℝ)^25 := by
    have hnat : (1580503447 : ℕ)^33*100000000000000^25 ≤ 54592021860391^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580503447 2500000000 54592021860391 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1237403767/10000000000 : ℝ), (2453241283/5000000000 : ℝ), (1580503447/2500000000 : ℝ)] ![(1585094289177/25000000000000 : ℝ), (19533800483773/50000000000000 : ℝ), (54592021860391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1237403767/10000000000 : ℝ)|^33 ≤ (1585094289177/25000000000000 : ℝ)^25
        have hw : |(-1237403767/10000000000 : ℝ)|=(1237403767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2453241283/5000000000 : ℝ)|^33 ≤ (19533800483773/50000000000000 : ℝ)^25
        have hw : |(2453241283/5000000000 : ℝ)|=(2453241283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1580503447/2500000000 : ℝ)|^33 ≤ (54592021860391/100000000000000 : ℝ)^25
        have hw : |(1580503447/2500000000 : ℝ)|=(1580503447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1981896243/5000000000 : ℝ)*x 0 + (-1464417423/10000000000 : ℝ)*x 1 + (7012965801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1981896243/5000000000 : ℝ)^33 ≤ (29478569261529/100000000000000 : ℝ)^25 := by
    have hnat : (1981896243 : ℕ)^33*100000000000000^25 ≤ 29478569261529^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981896243 5000000000 29478569261529 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1464417423/10000000000 : ℝ)^33 ≤ (30934114301/390625000000 : ℝ)^25 := by
    have hnat : (1464417423 : ℕ)^33*390625000000^25 ≤ 30934114301^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464417423 10000000000 30934114301 390625000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7012965801/10000000000 : ℝ)^33 ≤ (62602297457567/100000000000000 : ℝ)^25 := by
    have hnat : (7012965801 : ℕ)^33*100000000000000^25 ≤ 62602297457567^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7012965801 10000000000 62602297457567 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1981896243/5000000000 : ℝ), (-1464417423/10000000000 : ℝ), (7012965801/10000000000 : ℝ)] ![(29478569261529/100000000000000 : ℝ), (30934114301/390625000000 : ℝ), (62602297457567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1981896243/5000000000 : ℝ)|^33 ≤ (29478569261529/100000000000000 : ℝ)^25
        have hw : |(1981896243/5000000000 : ℝ)|=(1981896243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1464417423/10000000000 : ℝ)|^33 ≤ (30934114301/390625000000 : ℝ)^25
        have hw : |(-1464417423/10000000000 : ℝ)|=(1464417423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7012965801/10000000000 : ℝ)|^33 ≤ (62602297457567/100000000000000 : ℝ)^25
        have hw : |(7012965801/10000000000 : ℝ)|=(7012965801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (730397227/1250000000 : ℝ)*x 0 + (5598715759/10000000000 : ℝ)*x 1 + (-230352279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (730397227/1250000000 : ℝ)^33 ≤ (12300331731709/25000000000000 : ℝ)^25 := by
    have hnat : (730397227 : ℕ)^33*25000000000000^25 ≤ 12300331731709^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730397227 1250000000 12300331731709 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5598715759/10000000000 : ℝ)^33 ≤ (46502544130867/100000000000000 : ℝ)^25 := by
    have hnat : (5598715759 : ℕ)^33*100000000000000^25 ≤ 46502544130867^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598715759 10000000000 46502544130867 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230352279/2500000000 : ℝ)^33 ≤ (214806446377/5000000000000 : ℝ)^25 := by
    have hnat : (230352279 : ℕ)^33*5000000000000^25 ≤ 214806446377^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230352279 2500000000 214806446377 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(730397227/1250000000 : ℝ), (5598715759/10000000000 : ℝ), (-230352279/2500000000 : ℝ)] ![(12300331731709/25000000000000 : ℝ), (46502544130867/100000000000000 : ℝ), (214806446377/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(730397227/1250000000 : ℝ)|^33 ≤ (12300331731709/25000000000000 : ℝ)^25
        have hw : |(730397227/1250000000 : ℝ)|=(730397227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5598715759/10000000000 : ℝ)|^33 ≤ (46502544130867/100000000000000 : ℝ)^25
        have hw : |(5598715759/10000000000 : ℝ)|=(5598715759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-230352279/2500000000 : ℝ)|^33 ≤ (214806446377/5000000000000 : ℝ)^25
        have hw : |(-230352279/2500000000 : ℝ)|=(230352279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1982146829/2500000000 : ℝ)*x 0 + (1352214833/5000000000 : ℝ)*x 1 + (62315201/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1982146829/2500000000 : ℝ)^33 ≤ (14722056132811/20000000000000 : ℝ)^25 := by
    have hnat : (1982146829 : ℕ)^33*20000000000000^25 ≤ 14722056132811^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982146829 2500000000 14722056132811 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352214833/5000000000 : ℝ)^33 ≤ (3559343547649/20000000000000 : ℝ)^25 := by
    have hnat : (1352214833 : ℕ)^33*20000000000000^25 ≤ 3559343547649^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352214833 5000000000 3559343547649 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62315201/400000000 : ℝ)^33 ≤ (4296500790547/50000000000000 : ℝ)^25 := by
    have hnat : (62315201 : ℕ)^33*50000000000000^25 ≤ 4296500790547^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62315201 400000000 4296500790547 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1982146829/2500000000 : ℝ), (1352214833/5000000000 : ℝ), (62315201/400000000 : ℝ)] ![(14722056132811/20000000000000 : ℝ), (3559343547649/20000000000000 : ℝ), (4296500790547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1982146829/2500000000 : ℝ)|^33 ≤ (14722056132811/20000000000000 : ℝ)^25
        have hw : |(1982146829/2500000000 : ℝ)|=(1982146829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352214833/5000000000 : ℝ)|^33 ≤ (3559343547649/20000000000000 : ℝ)^25
        have hw : |(1352214833/5000000000 : ℝ)|=(1352214833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62315201/400000000 : ℝ)|^33 ≤ (4296500790547/50000000000000 : ℝ)^25
        have hw : |(62315201/400000000 : ℝ)|=(62315201/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-605139189/5000000000 : ℝ)*x 0 + (6022029257/10000000000 : ℝ)*x 1 + (524307239/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (605139189/5000000000 : ℝ)^33 ≤ (3078779362393/50000000000000 : ℝ)^25 := by
    have hnat : (605139189 : ℕ)^33*50000000000000^25 ≤ 3078779362393^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605139189 5000000000 3078779362393 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6022029257/10000000000 : ℝ)^33 ≤ (25599446838081/50000000000000 : ℝ)^25 := by
    have hnat : (6022029257 : ℕ)^33*50000000000000^25 ≤ 25599446838081^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6022029257 10000000000 25599446838081 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524307239/1000000000 : ℝ)^33 ≤ (10660886897793/25000000000000 : ℝ)^25 := by
    have hnat : (524307239 : ℕ)^33*25000000000000^25 ≤ 10660886897793^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524307239 1000000000 10660886897793 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-605139189/5000000000 : ℝ), (6022029257/10000000000 : ℝ), (524307239/1000000000 : ℝ)] ![(3078779362393/50000000000000 : ℝ), (25599446838081/50000000000000 : ℝ), (10660886897793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-605139189/5000000000 : ℝ)|^33 ≤ (3078779362393/50000000000000 : ℝ)^25
        have hw : |(-605139189/5000000000 : ℝ)|=(605139189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6022029257/10000000000 : ℝ)|^33 ≤ (25599446838081/50000000000000 : ℝ)^25
        have hw : |(6022029257/10000000000 : ℝ)|=(6022029257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524307239/1000000000 : ℝ)|^33 ≤ (10660886897793/25000000000000 : ℝ)^25
        have hw : |(524307239/1000000000 : ℝ)|=(524307239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5848581791/10000000000 : ℝ)*x 0 + (-883541369/10000000000 : ℝ)*x 1 + (224573827/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5848581791/10000000000 : ℝ)^33 ≤ (12315349978263/25000000000000 : ℝ)^25 := by
    have hnat : (5848581791 : ℕ)^33*25000000000000^25 ≤ 12315349978263^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5848581791 10000000000 12315349978263 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883541369/10000000000 : ℝ)^33 ≤ (20323078633/500000000000 : ℝ)^25 := by
    have hnat : (883541369 : ℕ)^33*500000000000^25 ≤ 20323078633^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883541369 10000000000 20323078633 500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224573827/400000000 : ℝ)^33 ≤ (9334796868211/20000000000000 : ℝ)^25 := by
    have hnat : (224573827 : ℕ)^33*20000000000000^25 ≤ 9334796868211^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224573827 400000000 9334796868211 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5848581791/10000000000 : ℝ), (-883541369/10000000000 : ℝ), (224573827/400000000 : ℝ)] ![(12315349978263/25000000000000 : ℝ), (20323078633/500000000000 : ℝ), (9334796868211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5848581791/10000000000 : ℝ)|^33 ≤ (12315349978263/25000000000000 : ℝ)^25
        have hw : |(5848581791/10000000000 : ℝ)|=(5848581791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-883541369/10000000000 : ℝ)|^33 ≤ (20323078633/500000000000 : ℝ)^25
        have hw : |(-883541369/10000000000 : ℝ)|=(883541369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224573827/400000000 : ℝ)|^33 ≤ (9334796868211/20000000000000 : ℝ)^25
        have hw : |(224573827/400000000 : ℝ)|=(224573827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3915605993/10000000000 : ℝ)*x 0 + (7062696477/10000000000 : ℝ)*x 1 + (-1448343647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3915605993/10000000000 : ℝ)^33 ≤ (29006455300019/100000000000000 : ℝ)^25 := by
    have hnat : (3915605993 : ℕ)^33*100000000000000^25 ≤ 29006455300019^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3915605993 10000000000 29006455300019 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7062696477/10000000000 : ℝ)^33 ≤ (15797236679299/25000000000000 : ℝ)^25 := by
    have hnat : (7062696477 : ℕ)^33*25000000000000^25 ≤ 15797236679299^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7062696477 10000000000 15797236679299 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1448343647/10000000000 : ℝ)^33 ≤ (7804597970883/100000000000000 : ℝ)^25 := by
    have hnat : (1448343647 : ℕ)^33*100000000000000^25 ≤ 7804597970883^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1448343647 10000000000 7804597970883 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3915605993/10000000000 : ℝ), (7062696477/10000000000 : ℝ), (-1448343647/10000000000 : ℝ)] ![(29006455300019/100000000000000 : ℝ), (15797236679299/25000000000000 : ℝ), (7804597970883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3915605993/10000000000 : ℝ)|^33 ≤ (29006455300019/100000000000000 : ℝ)^25
        have hw : |(3915605993/10000000000 : ℝ)|=(3915605993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7062696477/10000000000 : ℝ)|^33 ≤ (15797236679299/25000000000000 : ℝ)^25
        have hw : |(7062696477/10000000000 : ℝ)|=(7062696477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1448343647/10000000000 : ℝ)|^33 ≤ (7804597970883/100000000000000 : ℝ)^25
        have hw : |(-1448343647/10000000000 : ℝ)|=(1448343647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s6_s6_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4033618787/5000000000 : ℝ)*x 0 + (1064671819/5000000000 : ℝ)*x 1 + (246119179/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4033618787/5000000000 : ℝ)^33 ≤ (37657093968037/50000000000000 : ℝ)^25 := by
    have hnat : (4033618787 : ℕ)^33*50000000000000^25 ≤ 37657093968037^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033618787 5000000000 37657093968037 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064671819/5000000000 : ℝ)^33 ≤ (12980290014839/100000000000000 : ℝ)^25 := by
    have hnat : (1064671819 : ℕ)^33*100000000000000^25 ≤ 12980290014839^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064671819 5000000000 12980290014839 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246119179/1250000000 : ℝ)^33 ≤ (11705522039427/100000000000000 : ℝ)^25 := by
    have hnat : (246119179 : ℕ)^33*100000000000000^25 ≤ 11705522039427^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246119179 1250000000 11705522039427 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4033618787/5000000000 : ℝ), (1064671819/5000000000 : ℝ), (246119179/1250000000 : ℝ)] ![(37657093968037/50000000000000 : ℝ), (12980290014839/100000000000000 : ℝ), (11705522039427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4033618787/5000000000 : ℝ)|^33 ≤ (37657093968037/50000000000000 : ℝ)^25
        have hw : |(4033618787/5000000000 : ℝ)|=(4033618787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1064671819/5000000000 : ℝ)|^33 ≤ (12980290014839/100000000000000 : ℝ)^25
        have hw : |(1064671819/5000000000 : ℝ)|=(1064671819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(246119179/1250000000 : ℝ)|^33 ≤ (11705522039427/100000000000000 : ℝ)^25
        have hw : |(246119179/1250000000 : ℝ)|=(246119179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302053_s6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((55539/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(55539/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64833/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64833/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31871/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31871/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5027/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5027/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45991/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45991/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8919/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8919/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (55539/100000 : ℝ) ^ (65/16 : ℝ) ≤ (4585636296050844333/50000000000000000000 : ℝ) := by
    have hpowers : (55539/100000 : ℝ)^65 ≤ (4585636296050844333/50000000000000000000 : ℝ)^16 := by
      have hnat : (55539 : ℕ)^65*50000000000000000000^16 ≤ 4585636296050844333^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55539 100000 4585636296050844333 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (55539/100000 : ℝ)) (X := (4585636296050844333/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner0a : (54585636296050844333/50000000000000000000 : ℝ) ≤ (10218344081215709/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (54585636296050844333/50000000000000000000 : ℝ)^16 ≤ (10218344081215709/10000000000000000 : ℝ)^65 := by
      have hnat : (54585636296050844333 : ℕ)^16*10000000000000000^65 ≤ 10218344081215709^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54585636296050844333 50000000000000000000 10218344081215709 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10218344081215709/10000000000000000 : ℝ)) (X := (54585636296050844333/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner0b : (29585636296050844333/25000000000000000000 : ℝ) ≤ (10423268259410641/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (29585636296050844333/25000000000000000000 : ℝ)^16 ≤ (10423268259410641/10000000000000000 : ℝ)^65 := by
      have hnat : (29585636296050844333 : ℕ)^16*10000000000000000^65 ≤ 10423268259410641^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29585636296050844333 25000000000000000000 10423268259410641 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10423268259410641/10000000000000000 : ℝ)) (X := (29585636296050844333/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(12843769483277/326700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(51231044548733/1388475000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (55539/100000 : ℝ)) (alpha := (12843769483277/326700000000000 : ℝ)) (beta := (51231044548733/1388475000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (55539/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(12843769483277/326700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(51231044548733/1388475000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (64833/100000 : ℝ) ^ (65/16 : ℝ) ≤ (2149471754778083267/12500000000000000000 : ℝ) := by
    have hpowers : (64833/100000 : ℝ)^65 ≤ (2149471754778083267/12500000000000000000 : ℝ)^16 := by
      have hnat : (64833 : ℕ)^65*12500000000000000000^16 ≤ 2149471754778083267^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64833 100000 2149471754778083267 12500000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64833/100000 : ℝ)) (X := (2149471754778083267/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner1a : (14649471754778083267/12500000000000000000 : ℝ) ≤ (10398314339823441/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (14649471754778083267/12500000000000000000 : ℝ)^16 ≤ (10398314339823441/10000000000000000 : ℝ)^65 := by
      have hnat : (14649471754778083267 : ℕ)^16*10000000000000000^65 ≤ 10398314339823441^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14649471754778083267 12500000000000000000 10398314339823441 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10398314339823441/10000000000000000 : ℝ)) (X := (14649471754778083267/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner1b : (8399471754778083267/6250000000000000000 : ℝ) ≤ (10754723538573501/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (8399471754778083267/6250000000000000000 : ℝ)^16 ≤ (10754723538573501/10000000000000000 : ℝ)^65 := by
      have hnat : (8399471754778083267 : ℕ)^16*10000000000000000^65 ≤ 10754723538573501^65*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8399471754778083267 6250000000000000000 10754723538573501 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10754723538573501/10000000000000000 : ℝ)) (X := (8399471754778083267/6250000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(398314339823441/6483300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(5940153312501/108055000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (64833/100000 : ℝ)) (alpha := (398314339823441/6483300000000000 : ℝ)) (beta := (5940153312501/108055000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (64833/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(398314339823441/6483300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(5940153312501/108055000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (31871/50000 : ℝ) ^ (65/16 : ℝ) ≤ (16050159378576184481/100000000000000000000 : ℝ) := by
    have hpowers : (31871/50000 : ℝ)^65 ≤ (16050159378576184481/100000000000000000000 : ℝ)^16 := by
      have hnat : (31871 : ℕ)^65*100000000000000000000^16 ≤ 16050159378576184481^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31871 50000 16050159378576184481 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31871/50000 : ℝ)) (X := (16050159378576184481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner2a : (116050159378576184481/100000000000000000000 : ℝ) ≤ (103732011099817/100000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (116050159378576184481/100000000000000000000 : ℝ)^16 ≤ (103732011099817/100000000000000 : ℝ)^65 := by
      have hnat : (116050159378576184481 : ℕ)^16*100000000000000^65 ≤ 103732011099817^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116050159378576184481 100000000000000000000 103732011099817 100000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (103732011099817/100000000000000 : ℝ)) (X := (116050159378576184481/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner2b : (66050159378576184481/50000000000000000000 : ℝ) ≤ (10709296717380661/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (66050159378576184481/50000000000000000000 : ℝ)^16 ≤ (10709296717380661/10000000000000000 : ℝ)^65 := by
      have hnat : (66050159378576184481 : ℕ)^16*10000000000000000^65 ≤ 10709296717380661^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66050159378576184481 50000000000000000000 10709296717380661 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10709296717380661/10000000000000000 : ℝ)) (X := (66050159378576184481/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(533144442831/9106000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(336095607398961/6374200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (31871/50000 : ℝ)) (alpha := (533144442831/9106000000000 : ℝ)) (beta := (336095607398961/6374200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (31871/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(533144442831/9106000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(336095607398961/6374200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-2404048003/10000000000 : ℝ)*X 0 0+(2600119757/5000000000 : ℝ)*X 0 1+(1309302393/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((4586981983/10000000000 : ℝ)*X 2 0+(772444413/1250000000 : ℝ)*X 2 1+(-38291983/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((6619094381/10000000000 : ℝ)*X 0 0+(386238687/1250000000 : ℝ)*X 0 1+(1520521973/5000000000 : ℝ)*X 0 2+(6619094381/10000000000 : ℝ)*X 1 0+(386238687/1250000000 : ℝ)*X 1 1+(1520521973/5000000000 : ℝ)*X 1 2+(6619094381/10000000000 : ℝ)*X 2 0+(386238687/1250000000 : ℝ)*X 2 1+(1520521973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-453418291/2000000000 : ℝ)*X 0 0+(1031149481/2500000000 : ℝ)*X 0 1+(6343115949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((4063170851/10000000000 : ℝ)*X 1 0+(-80555427/625000000 : ℝ)*X 1 1+(3517034447/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((2042445317/5000000000 : ℝ)*X 2 0+(45181153/62500000 : ℝ)*X 2 1+(-180061053/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((6286375247/10000000000 : ℝ)*X 0 0+(2379464633/5000000000 : ℝ)*X 0 1+(758012033/5000000000 : ℝ)*X 0 2+(6286375247/10000000000 : ℝ)*X 1 0+(2379464633/5000000000 : ℝ)*X 1 1+(758012033/5000000000 : ℝ)*X 1 2+(6286375247/10000000000 : ℝ)*X 2 0+(2379464633/5000000000 : ℝ)*X 2 1+(758012033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-1237403767/10000000000 : ℝ)*X 0 0+(2453241283/5000000000 : ℝ)*X 0 1+(1580503447/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((1981896243/5000000000 : ℝ)*X 1 0+(-1464417423/10000000000 : ℝ)*X 1 1+(7012965801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((730397227/1250000000 : ℝ)*X 2 0+(5598715759/10000000000 : ℝ)*X 2 1+(-230352279/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((1982146829/2500000000 : ℝ)*X 0 0+(1352214833/5000000000 : ℝ)*X 0 1+(62315201/400000000 : ℝ)*X 0 2+(1982146829/2500000000 : ℝ)*X 1 0+(1352214833/5000000000 : ℝ)*X 1 1+(62315201/400000000 : ℝ)*X 1 2+(1982146829/2500000000 : ℝ)*X 2 0+(1352214833/5000000000 : ℝ)*X 2 1+(62315201/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-605139189/5000000000 : ℝ)*X 0 0+(6022029257/10000000000 : ℝ)*X 0 1+(524307239/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((5848581791/10000000000 : ℝ)*X 1 0+(-883541369/10000000000 : ℝ)*X 1 1+(224573827/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((3915605993/10000000000 : ℝ)*X 2 0+(7062696477/10000000000 : ℝ)*X 2 1+(-1448343647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((4033618787/5000000000 : ℝ)*X 0 0+(1064671819/5000000000 : ℝ)*X 0 1+(246119179/1250000000 : ℝ)*X 0 2+(4033618787/5000000000 : ℝ)*X 1 0+(1064671819/5000000000 : ℝ)*X 1 1+(246119179/1250000000 : ℝ)*X 1 2+(4033618787/5000000000 : ℝ)*X 2 0+(1064671819/5000000000 : ℝ)*X 2 1+(246119179/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((5027/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5027/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (79237164152562455656797970597/5000427954060000000000000000000000 : ℝ) := by norm_num
    linear_combination (3410297/500000000000 : ℝ)*(base49) + (165693716877/500000000000 : ℝ)*(base59) + (607369/500000000000 : ℝ)*(base60) + (4151211405171/1000000000000 : ℝ)*(major_s6_0) + (4151211405171/1000000000000 : ℝ)*(major_s6_1) + (4151211405171/1000000000000 : ℝ)*(major_s6_2) + (73302849/1000000000000 : ℝ)*(sp_s6_0) + (16293861/500000000000 : ℝ)*(sp_s6_6) + (1103894278467/200000000000 : ℝ)*(sp_s6_7) + (1379784467173/250000000000 : ℝ)*(sp_s6_8) + (344957734643/62500000000 : ℝ)*(sp_s6_9) + (2782840245403/1000000000000 : ℝ)*(sp_s6_13) + (101706623/250000000000 : ℝ)*(sp_s6_15) + (220940897/1000000000000 : ℝ)*(sp_s6_23) + (695718208281/250000000000 : ℝ)*(f.failure) + (1103908939037/200000000000 : ℝ)*(f.sum) + (6766570295300946019/9839488300000000000000000000000 : ℝ)*base62 + (1489149681058451/6374200000000000000000000000 : ℝ)*base64 + (3291849191087/8644400000000000000000000 : ℝ)*base67 + (12442648252113/22765000000000000000000000 : ℝ)*base68 + (2385449430872960021/6941503800000000000000000000000 : ℝ)*base70 + (7198330680547/231412500000000000000000000 : ℝ)*base72 + (2173033415737823/2161100000000000000000000000 : ℝ)*base74 + (95266290001121/108900000000000000000000000 : ℝ)*base76 + (6163413533776180987/20004222150000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (177/2500000000000000 : ℝ)*base87 + (177/2500000000000000 : ℝ)*base89 + (177/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45991/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45991/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (100374148956826473057802599947/15001283862180000000000000000000000 : ℝ) := by norm_num
    linear_combination (467427/500000000000 : ℝ)*(base19) + (67629/500000000000 : ℝ)*(base39) + (1219919/500000000000 : ℝ)*(base59) + (809720307089/200000000000 : ℝ)*(major_s6_0) + (809720307089/200000000000 : ℝ)*(major_s6_1) + (809720307089/200000000000 : ℝ)*(major_s6_2) + (5944371/1000000000000 : ℝ)*(sp_s6_0) + (3309511/250000000000 : ℝ)*(sp_s6_2) + (1365643/40000000000 : ℝ)*(sp_s6_7) + (1345768781077/250000000000 : ℝ)*(sp_s6_14) + (5383114274899/1000000000000 : ℝ)*(sp_s6_15) + (538310197171/100000000000 : ℝ)*(sp_s6_16) + (678510562793/250000000000 : ℝ)*(sp_s6_20) + (8675923/200000000000 : ℝ)*(sp_s6_27) + (2714085630787/1000000000000 : ℝ)*(f.failure) + (5383115209753/1000000000000 : ℝ)*(f.sum) + (549148998897836423/5903692980000000000000000000000 : ℝ)*base63 + (4279319280197/10198720000000000000000000 : ℝ)*base64 + (44008908351271/216110000000000000000000000 : ℝ)*base66 + (11229824826347/45530000000000000000000000 : ℝ)*base69 + (1207699700092355777/4164902280000000000000000000000 : ℝ)*base70 + (67428350025893/555390000000000000000000000 : ℝ)*base73 + (62259277693087/259332000000000000000000000 : ℝ)*base74 + (14944070491739/65340000000000000000000000 : ℝ)*base76 + (750317116604978669/3000633322500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (321/10000000000000000 : ℝ)*base86 + (321/10000000000000000 : ℝ)*base88 + (321/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8919/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8919/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4539692298366155967687823/555672837500000000000000000000 : ℝ) := by norm_num
    linear_combination (163547675527/1000000000000 : ℝ)*(base40) + (311647/125000000000 : ℝ)*(base49) + (14704437259/1000000000000 : ℝ)*(base59) + (1923816048273/500000000000 : ℝ)*(major_s6_0) + (1923816048273/500000000000 : ℝ)*(major_s6_1) + (1923816048273/500000000000 : ℝ)*(major_s6_2) + (9547847/500000000000 : ℝ)*(sp_s6_0) + (10697271/200000000000 : ℝ)*(sp_s6_2) + (20901811/500000000000 : ℝ)*(sp_s6_9) + (71402449/500000000000 : ℝ)*(sp_s6_20) + (2557940924107/500000000000 : ℝ)*(sp_s6_21) + (1278975235977/250000000000 : ℝ)*(sp_s6_22) + (5115805653931/1000000000000 : ℝ)*(sp_s6_23) + (2579217721043/1000000000000 : ℝ)*(sp_s6_27) + (2579360525941/1000000000000 : ℝ)*(f.failure) + (1278975235977/250000000000 : ℝ)*(f.sum) + (1128274275945998447/4919744150000000000000000000000 : ℝ)*base62 + (125613565462041/455300000000000000000000000 : ℝ)*base65 + (58227412029757/108055000000000000000000000 : ℝ)*base67 + (368004965981/2845625000000000000000000 : ℝ)*base69 + (31961931894040063/165273900000000000000000000000 : ℝ)*base70 + (59390541758437/154275000000000000000000000 : ℝ)*base73 + (148461538057601/1080550000000000000000000000 : ℝ)*base75 + (2821219649917/9075000000000000000000000 : ℝ)*base77 + (851683690271915839/6668074050000000000000000000000 : ℝ)*base79 + (1897/10000000000000000 : ℝ)*base87 + (1897/10000000000000000 : ℝ)*base89 + (1897/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((55539/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(55539/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64833/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64833/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31871/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31871/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5027/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5027/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45991/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45991/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8919/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8919/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302053_s6 p hpa hpb X hX hprev5

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308075_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:39:38.534363+00:00
-- url     : https://prove2.me/submissions/30cd7b6b-fd14-4f3b-9c6e-ed38ea8a4355

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
theorem collision_support_c308075_s2_s2_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-768620699/5000000000 : ℝ)*x 0 + (-2939652729/5000000000 : ℝ)*x 1 + (5058917331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (768620699/5000000000 : ℝ)^69 ≤ (8734343025743/100000000000000 : ℝ)^53 := by
    have hnat : (768620699 : ℕ)^69*100000000000000^53 ≤ 8734343025743^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768620699 5000000000 8734343025743 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2939652729/5000000000 : ℝ)^69 ≤ (50082799619697/100000000000000 : ℝ)^53 := by
    have hnat : (2939652729 : ℕ)^69*100000000000000^53 ≤ 50082799619697^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939652729 5000000000 50082799619697 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5058917331/10000000000 : ℝ)^69 ≤ (41182857335187/100000000000000 : ℝ)^53 := by
    have hnat : (5058917331 : ℕ)^69*100000000000000^53 ≤ 41182857335187^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5058917331 10000000000 41182857335187 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-768620699/5000000000 : ℝ), (-2939652729/5000000000 : ℝ), (5058917331/10000000000 : ℝ)] ![(8734343025743/100000000000000 : ℝ), (50082799619697/100000000000000 : ℝ), (41182857335187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-768620699/5000000000 : ℝ)|^69 ≤ (8734343025743/100000000000000 : ℝ)^53
        have hw : |(-768620699/5000000000 : ℝ)|=(768620699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2939652729/5000000000 : ℝ)|^69 ≤ (50082799619697/100000000000000 : ℝ)^53
        have hw : |(-2939652729/5000000000 : ℝ)|=(2939652729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5058917331/10000000000 : ℝ)|^69 ≤ (41182857335187/100000000000000 : ℝ)^53
        have hw : |(5058917331/10000000000 : ℝ)|=(5058917331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2574828869/5000000000 : ℝ)*x 0 + (-2040175763/5000000000 : ℝ)*x 1 + (-3628990161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2574828869/5000000000 : ℝ)^69 ≤ (42147135232689/100000000000000 : ℝ)^53 := by
    have hnat : (2574828869 : ℕ)^69*100000000000000^53 ≤ 42147135232689^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574828869 5000000000 42147135232689 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040175763/5000000000 : ℝ)^69 ≤ (31129512575189/100000000000000 : ℝ)^53 := by
    have hnat : (2040175763 : ℕ)^69*100000000000000^53 ≤ 31129512575189^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040175763 5000000000 31129512575189 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3628990161/10000000000 : ℝ)^69 ≤ (26723352176373/100000000000000 : ℝ)^53 := by
    have hnat : (3628990161 : ℕ)^69*100000000000000^53 ≤ 26723352176373^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3628990161 10000000000 26723352176373 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2574828869/5000000000 : ℝ), (-2040175763/5000000000 : ℝ), (-3628990161/10000000000 : ℝ)] ![(42147135232689/100000000000000 : ℝ), (31129512575189/100000000000000 : ℝ), (26723352176373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2574828869/5000000000 : ℝ)|^69 ≤ (42147135232689/100000000000000 : ℝ)^53
        have hw : |(2574828869/5000000000 : ℝ)|=(2574828869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2040175763/5000000000 : ℝ)|^69 ≤ (31129512575189/100000000000000 : ℝ)^53
        have hw : |(-2040175763/5000000000 : ℝ)|=(2040175763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3628990161/10000000000 : ℝ)|^69 ≤ (26723352176373/100000000000000 : ℝ)^53
        have hw : |(-3628990161/10000000000 : ℝ)|=(3628990161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3457447447/10000000000 : ℝ)*x 0 + (-2923506731/10000000000 : ℝ)*x 1 + (3147491703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3457447447/10000000000 : ℝ)^69 ≤ (25090654567409/100000000000000 : ℝ)^53 := by
    have hnat : (3457447447 : ℕ)^69*100000000000000^53 ≤ 25090654567409^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3457447447 10000000000 25090654567409 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2923506731/10000000000 : ℝ)^69 ≤ (20168221360773/100000000000000 : ℝ)^53 := by
    have hnat : (2923506731 : ℕ)^69*100000000000000^53 ≤ 20168221360773^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2923506731 10000000000 20168221360773 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3147491703/5000000000 : ℝ)^69 ≤ (13685281014847/25000000000000 : ℝ)^53 := by
    have hnat : (3147491703 : ℕ)^69*25000000000000^53 ≤ 13685281014847^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3147491703 5000000000 13685281014847 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3457447447/10000000000 : ℝ), (-2923506731/10000000000 : ℝ), (3147491703/5000000000 : ℝ)] ![(25090654567409/100000000000000 : ℝ), (20168221360773/100000000000000 : ℝ), (13685281014847/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3457447447/10000000000 : ℝ)|^69 ≤ (25090654567409/100000000000000 : ℝ)^53
        have hw : |(3457447447/10000000000 : ℝ)|=(3457447447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2923506731/10000000000 : ℝ)|^69 ≤ (20168221360773/100000000000000 : ℝ)^53
        have hw : |(-2923506731/10000000000 : ℝ)|=(2923506731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3147491703/5000000000 : ℝ)|^69 ≤ (13685281014847/25000000000000 : ℝ)^53
        have hw : |(3147491703/5000000000 : ℝ)|=(3147491703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-17043139/125000000 : ℝ)*x 0 + (-6565825963/10000000000 : ℝ)*x 1 + (887083841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17043139/125000000 : ℝ)^69 ≤ (1867835812833/25000000000000 : ℝ)^53 := by
    have hnat : (17043139 : ℕ)^69*25000000000000^53 ≤ 1867835812833^53*125000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17043139 125000000 1867835812833 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6565825963/10000000000 : ℝ)^69 ≤ (57827103562793/100000000000000 : ℝ)^53 := by
    have hnat : (6565825963 : ℕ)^69*100000000000000^53 ≤ 57827103562793^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6565825963 10000000000 57827103562793 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (887083841/2000000000 : ℝ)^69 ≤ (6940310634611/20000000000000 : ℝ)^53 := by
    have hnat : (887083841 : ℕ)^69*20000000000000^53 ≤ 6940310634611^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887083841 2000000000 6940310634611 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17043139/125000000 : ℝ), (-6565825963/10000000000 : ℝ), (887083841/2000000000 : ℝ)] ![(1867835812833/25000000000000 : ℝ), (57827103562793/100000000000000 : ℝ), (6940310634611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17043139/125000000 : ℝ)|^69 ≤ (1867835812833/25000000000000 : ℝ)^53
        have hw : |(-17043139/125000000 : ℝ)|=(17043139/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6565825963/10000000000 : ℝ)|^69 ≤ (57827103562793/100000000000000 : ℝ)^53
        have hw : |(-6565825963/10000000000 : ℝ)|=(6565825963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(887083841/2000000000 : ℝ)|^69 ≤ (6940310634611/20000000000000 : ℝ)^53
        have hw : |(887083841/2000000000 : ℝ)|=(887083841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6313862671/10000000000 : ℝ)*x 0 + (818119521/2500000000 : ℝ)*x 1 + (3091250351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6313862671/10000000000 : ℝ)^69 ≤ (10990991324929/20000000000000 : ℝ)^53 := by
    have hnat : (6313862671 : ℕ)^69*20000000000000^53 ≤ 10990991324929^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6313862671 10000000000 10990991324929 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (818119521/2500000000 : ℝ)^69 ≤ (23357397078637/100000000000000 : ℝ)^53 := by
    have hnat : (818119521 : ℕ)^69*100000000000000^53 ≤ 23357397078637^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818119521 2500000000 23357397078637 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3091250351/10000000000 : ℝ)^69 ≤ (21687646275271/100000000000000 : ℝ)^53 := by
    have hnat : (3091250351 : ℕ)^69*100000000000000^53 ≤ 21687646275271^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091250351 10000000000 21687646275271 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6313862671/10000000000 : ℝ), (818119521/2500000000 : ℝ), (3091250351/10000000000 : ℝ)] ![(10990991324929/20000000000000 : ℝ), (23357397078637/100000000000000 : ℝ), (21687646275271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6313862671/10000000000 : ℝ)|^69 ≤ (10990991324929/20000000000000 : ℝ)^53
        have hw : |(6313862671/10000000000 : ℝ)|=(6313862671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(818119521/2500000000 : ℝ)|^69 ≤ (23357397078637/100000000000000 : ℝ)^53
        have hw : |(818119521/2500000000 : ℝ)|=(818119521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3091250351/10000000000 : ℝ)|^69 ≤ (21687646275271/100000000000000 : ℝ)^53
        have hw : |(3091250351/10000000000 : ℝ)|=(3091250351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5377023727/10000000000 : ℝ)*x 0 + (-486182271/1250000000 : ℝ)*x 1 + (-714167389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377023727/10000000000 : ℝ)^69 ≤ (44585755215121/100000000000000 : ℝ)^53 := by
    have hnat : (5377023727 : ℕ)^69*100000000000000^53 ≤ 44585755215121^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377023727 10000000000 44585755215121 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486182271/1250000000 : ℝ)^69 ≤ (14623524147381/50000000000000 : ℝ)^53 := by
    have hnat : (486182271 : ℕ)^69*50000000000000^53 ≤ 14623524147381^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486182271 1250000000 14623524147381 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (714167389/2000000000 : ℝ)^69 ≤ (1046687858683/4000000000000 : ℝ)^53 := by
    have hnat : (714167389 : ℕ)^69*4000000000000^53 ≤ 1046687858683^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714167389 2000000000 1046687858683 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377023727/10000000000 : ℝ), (-486182271/1250000000 : ℝ), (-714167389/2000000000 : ℝ)] ![(44585755215121/100000000000000 : ℝ), (14623524147381/50000000000000 : ℝ), (1046687858683/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377023727/10000000000 : ℝ)|^69 ≤ (44585755215121/100000000000000 : ℝ)^53
        have hw : |(5377023727/10000000000 : ℝ)|=(5377023727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486182271/1250000000 : ℝ)|^69 ≤ (14623524147381/50000000000000 : ℝ)^53
        have hw : |(-486182271/1250000000 : ℝ)|=(486182271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-714167389/2000000000 : ℝ)|^69 ≤ (1046687858683/4000000000000 : ℝ)^53
        have hw : |(-714167389/2000000000 : ℝ)|=(714167389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2528207379/10000000000 : ℝ)*x 0 + (-127758591/625000000 : ℝ)*x 1 + (191441981/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2528207379/10000000000 : ℝ)^69 ≤ (521650653883/3125000000000 : ℝ)^53 := by
    have hnat : (2528207379 : ℕ)^69*3125000000000^53 ≤ 521650653883^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528207379 10000000000 521650653883 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127758591/625000000 : ℝ)^69 ≤ (6328957873879/50000000000000 : ℝ)^53 := by
    have hnat : (127758591 : ℕ)^69*50000000000000^53 ≤ 6328957873879^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127758591 625000000 6328957873879 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191441981/250000000 : ℝ)^69 ≤ (220778947847/312500000000 : ℝ)^53 := by
    have hnat : (191441981 : ℕ)^69*312500000000^53 ≤ 220778947847^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191441981 250000000 220778947847 312500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2528207379/10000000000 : ℝ), (-127758591/625000000 : ℝ), (191441981/250000000 : ℝ)] ![(521650653883/3125000000000 : ℝ), (6328957873879/50000000000000 : ℝ), (220778947847/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2528207379/10000000000 : ℝ)|^69 ≤ (521650653883/3125000000000 : ℝ)^53
        have hw : |(2528207379/10000000000 : ℝ)|=(2528207379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127758591/625000000 : ℝ)|^69 ≤ (6328957873879/50000000000000 : ℝ)^53
        have hw : |(-127758591/625000000 : ℝ)|=(127758591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(191441981/250000000 : ℝ)|^69 ≤ (220778947847/312500000000 : ℝ)^53
        have hw : |(191441981/250000000 : ℝ)|=(191441981/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1041474153/10000000000 : ℝ)*x 0 + (-1436586317/2500000000 : ℝ)*x 1 + (5519087173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041474153/10000000000 : ℝ)^69 ≤ (65765717817/1250000000000 : ℝ)^53 := by
    have hnat : (1041474153 : ℕ)^69*1250000000000^53 ≤ 65765717817^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041474153 10000000000 65765717817 1250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1436586317/2500000000 : ℝ)^69 ≤ (48613316900819/100000000000000 : ℝ)^53 := by
    have hnat : (1436586317 : ℕ)^69*100000000000000^53 ≤ 48613316900819^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1436586317 2500000000 48613316900819 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5519087173/10000000000 : ℝ)^69 ≤ (5765678206581/12500000000000 : ℝ)^53 := by
    have hnat : (5519087173 : ℕ)^69*12500000000000^53 ≤ 5765678206581^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519087173 10000000000 5765678206581 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1041474153/10000000000 : ℝ), (-1436586317/2500000000 : ℝ), (5519087173/10000000000 : ℝ)] ![(65765717817/1250000000000 : ℝ), (48613316900819/100000000000000 : ℝ), (5765678206581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1041474153/10000000000 : ℝ)|^69 ≤ (65765717817/1250000000000 : ℝ)^53
        have hw : |(-1041474153/10000000000 : ℝ)|=(1041474153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1436586317/2500000000 : ℝ)|^69 ≤ (48613316900819/100000000000000 : ℝ)^53
        have hw : |(-1436586317/2500000000 : ℝ)|=(1436586317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5519087173/10000000000 : ℝ)|^69 ≤ (5765678206581/12500000000000 : ℝ)^53
        have hw : |(5519087173/10000000000 : ℝ)|=(5519087173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (685914481/1000000000 : ℝ)*x 0 + (3113183557/10000000000 : ℝ)*x 1 + (159510193/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685914481/1000000000 : ℝ)^69 ≤ (61212770856289/100000000000000 : ℝ)^53 := by
    have hnat : (685914481 : ℕ)^69*100000000000000^53 ≤ 61212770856289^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685914481 1000000000 61212770856289 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3113183557/10000000000 : ℝ)^69 ≤ (10944096988439/50000000000000 : ℝ)^53 := by
    have hnat : (3113183557 : ℕ)^69*50000000000000^53 ≤ 10944096988439^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3113183557 10000000000 10944096988439 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159510193/625000000 : ℝ)^69 ≤ (8449517577271/50000000000000 : ℝ)^53 := by
    have hnat : (159510193 : ℕ)^69*50000000000000^53 ≤ 8449517577271^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159510193 625000000 8449517577271 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685914481/1000000000 : ℝ), (3113183557/10000000000 : ℝ), (159510193/625000000 : ℝ)] ![(61212770856289/100000000000000 : ℝ), (10944096988439/50000000000000 : ℝ), (8449517577271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685914481/1000000000 : ℝ)|^69 ≤ (61212770856289/100000000000000 : ℝ)^53
        have hw : |(685914481/1000000000 : ℝ)|=(685914481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3113183557/10000000000 : ℝ)|^69 ≤ (10944096988439/50000000000000 : ℝ)^53
        have hw : |(3113183557/10000000000 : ℝ)|=(3113183557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159510193/625000000 : ℝ)|^69 ≤ (8449517577271/50000000000000 : ℝ)^53
        have hw : |(159510193/625000000 : ℝ)|=(159510193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1103410377/2000000000 : ℝ)*x 0 + (-4133732497/10000000000 : ℝ)*x 1 + (-3151108341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103410377/2000000000 : ℝ)^69 ≤ (23051641030879/50000000000000 : ℝ)^53 := by
    have hnat : (1103410377 : ℕ)^69*50000000000000^53 ≤ 23051641030879^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103410377 2000000000 23051641030879 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4133732497/10000000000 : ℝ)^69 ≤ (3166074992263/10000000000000 : ℝ)^53 := by
    have hnat : (4133732497 : ℕ)^69*10000000000000^53 ≤ 3166074992263^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133732497 10000000000 3166074992263 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3151108341/10000000000 : ℝ)^69 ≤ (11117983997707/50000000000000 : ℝ)^53 := by
    have hnat : (3151108341 : ℕ)^69*50000000000000^53 ≤ 11117983997707^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3151108341 10000000000 11117983997707 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103410377/2000000000 : ℝ), (-4133732497/10000000000 : ℝ), (-3151108341/10000000000 : ℝ)] ![(23051641030879/50000000000000 : ℝ), (3166074992263/10000000000000 : ℝ), (11117983997707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103410377/2000000000 : ℝ)|^69 ≤ (23051641030879/50000000000000 : ℝ)^53
        have hw : |(1103410377/2000000000 : ℝ)|=(1103410377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4133732497/10000000000 : ℝ)|^69 ≤ (3166074992263/10000000000000 : ℝ)^53
        have hw : |(-4133732497/10000000000 : ℝ)|=(4133732497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3151108341/10000000000 : ℝ)|^69 ≤ (11117983997707/50000000000000 : ℝ)^53
        have hw : |(-3151108341/10000000000 : ℝ)|=(3151108341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1352968887/5000000000 : ℝ)*x 0 + (-1122324447/5000000000 : ℝ)*x 1 + (1478243289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352968887/5000000000 : ℝ)^69 ≤ (3647304681411/20000000000000 : ℝ)^53 := by
    have hnat : (1352968887 : ℕ)^69*20000000000000^53 ≤ 3647304681411^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352968887 5000000000 3647304681411 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122324447/5000000000 : ℝ)^69 ≤ (14297782822799/100000000000000 : ℝ)^53 := by
    have hnat : (1122324447 : ℕ)^69*100000000000000^53 ≤ 14297782822799^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122324447 5000000000 14297782822799 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1478243289/2000000000 : ℝ)^69 ≤ (33732846883733/50000000000000 : ℝ)^53 := by
    have hnat : (1478243289 : ℕ)^69*50000000000000^53 ≤ 33732846883733^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1478243289 2000000000 33732846883733 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352968887/5000000000 : ℝ), (-1122324447/5000000000 : ℝ), (1478243289/2000000000 : ℝ)] ![(3647304681411/20000000000000 : ℝ), (14297782822799/100000000000000 : ℝ), (33732846883733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352968887/5000000000 : ℝ)|^69 ≤ (3647304681411/20000000000000 : ℝ)^53
        have hw : |(1352968887/5000000000 : ℝ)|=(1352968887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1122324447/5000000000 : ℝ)|^69 ≤ (14297782822799/100000000000000 : ℝ)^53
        have hw : |(-1122324447/5000000000 : ℝ)|=(1122324447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1478243289/2000000000 : ℝ)|^69 ≤ (33732846883733/50000000000000 : ℝ)^53
        have hw : |(1478243289/2000000000 : ℝ)|=(1478243289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1008753141/10000000000 : ℝ)*x 0 + (-804494289/1250000000 : ℝ)*x 1 + (4814392937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008753141/10000000000 : ℝ)^69 ≤ (5047086161699/100000000000000 : ℝ)^53 := by
    have hnat : (1008753141 : ℕ)^69*100000000000000^53 ≤ 5047086161699^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008753141 10000000000 5047086161699 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804494289/1250000000 : ℝ)^69 ≤ (2253698013353/4000000000000 : ℝ)^53 := by
    have hnat : (804494289 : ℕ)^69*4000000000000^53 ≤ 2253698013353^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804494289 1250000000 2253698013353 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4814392937/10000000000 : ℝ)^69 ≤ (19305231743269/50000000000000 : ℝ)^53 := by
    have hnat : (4814392937 : ℕ)^69*50000000000000^53 ≤ 19305231743269^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814392937 10000000000 19305231743269 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1008753141/10000000000 : ℝ), (-804494289/1250000000 : ℝ), (4814392937/10000000000 : ℝ)] ![(5047086161699/100000000000000 : ℝ), (2253698013353/4000000000000 : ℝ), (19305231743269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1008753141/10000000000 : ℝ)|^69 ≤ (5047086161699/100000000000000 : ℝ)^53
        have hw : |(-1008753141/10000000000 : ℝ)|=(1008753141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-804494289/1250000000 : ℝ)|^69 ≤ (2253698013353/4000000000000 : ℝ)^53
        have hw : |(-804494289/1250000000 : ℝ)|=(804494289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4814392937/10000000000 : ℝ)|^69 ≤ (19305231743269/50000000000000 : ℝ)^53
        have hw : |(4814392937/10000000000 : ℝ)|=(4814392937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1738063381/2500000000 : ℝ)*x 0 + (2888956231/10000000000 : ℝ)*x 1 + (2661177133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1738063381/2500000000 : ℝ)^69 ≤ (389354700677/625000000000 : ℝ)^53 := by
    have hnat : (1738063381 : ℕ)^69*625000000000^53 ≤ 389354700677^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738063381 2500000000 389354700677 625000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2888956231/10000000000 : ℝ)^69 ≤ (19858469805873/100000000000000 : ℝ)^53 := by
    have hnat : (2888956231 : ℕ)^69*100000000000000^53 ≤ 19858469805873^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2888956231 10000000000 19858469805873 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2661177133/10000000000 : ℝ)^69 ≤ (4461194520437/25000000000000 : ℝ)^53 := by
    have hnat : (2661177133 : ℕ)^69*25000000000000^53 ≤ 4461194520437^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2661177133 10000000000 4461194520437 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1738063381/2500000000 : ℝ), (2888956231/10000000000 : ℝ), (2661177133/10000000000 : ℝ)] ![(389354700677/625000000000 : ℝ), (19858469805873/100000000000000 : ℝ), (4461194520437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1738063381/2500000000 : ℝ)|^69 ≤ (389354700677/625000000000 : ℝ)^53
        have hw : |(1738063381/2500000000 : ℝ)|=(1738063381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2888956231/10000000000 : ℝ)|^69 ≤ (19858469805873/100000000000000 : ℝ)^53
        have hw : |(2888956231/10000000000 : ℝ)|=(2888956231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2661177133/10000000000 : ℝ)|^69 ≤ (4461194520437/25000000000000 : ℝ)^53
        have hw : |(2661177133/10000000000 : ℝ)|=(2661177133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4940321581/10000000000 : ℝ)*x 0 + (-130743669/312500000 : ℝ)*x 1 + (-3752007951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4940321581/10000000000 : ℝ)^69 ≤ (39930427968127/100000000000000 : ℝ)^53 := by
    have hnat : (4940321581 : ℕ)^69*100000000000000^53 ≤ 39930427968127^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4940321581 10000000000 39930427968127 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130743669/312500000 : ℝ)^69 ≤ (804021813471/2500000000000 : ℝ)^53 := by
    have hnat : (130743669 : ℕ)^69*2500000000000^53 ≤ 804021813471^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130743669 312500000 804021813471 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3752007951/10000000000 : ℝ)^69 ≤ (13954349735827/50000000000000 : ℝ)^53 := by
    have hnat : (3752007951 : ℕ)^69*50000000000000^53 ≤ 13954349735827^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752007951 10000000000 13954349735827 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4940321581/10000000000 : ℝ), (-130743669/312500000 : ℝ), (-3752007951/10000000000 : ℝ)] ![(39930427968127/100000000000000 : ℝ), (804021813471/2500000000000 : ℝ), (13954349735827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4940321581/10000000000 : ℝ)|^69 ≤ (39930427968127/100000000000000 : ℝ)^53
        have hw : |(4940321581/10000000000 : ℝ)|=(4940321581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130743669/312500000 : ℝ)|^69 ≤ (804021813471/2500000000000 : ℝ)^53
        have hw : |(-130743669/312500000 : ℝ)|=(130743669/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3752007951/10000000000 : ℝ)|^69 ≤ (13954349735827/50000000000000 : ℝ)^53
        have hw : |(-3752007951/10000000000 : ℝ)|=(3752007951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308075_s2_s2_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (761585517/2000000000 : ℝ)*x 0 + (-2511646513/10000000000 : ℝ)*x 1 + (157941437/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (761585517/2000000000 : ℝ)^69 ≤ (3556429014357/12500000000000 : ℝ)^53 := by
    have hnat : (761585517 : ℕ)^69*12500000000000^53 ≤ 3556429014357^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761585517 2000000000 3556429014357 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2511646513/10000000000 : ℝ)^69 ≤ (16550606702827/100000000000000 : ℝ)^53 := by
    have hnat : (2511646513 : ℕ)^69*100000000000000^53 ≤ 16550606702827^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511646513 10000000000 16550606702827 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157941437/250000000 : ℝ)^69 ≤ (54997961161351/100000000000000 : ℝ)^53 := by
    have hnat : (157941437 : ℕ)^69*100000000000000^53 ≤ 54997961161351^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157941437 250000000 54997961161351 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(761585517/2000000000 : ℝ), (-2511646513/10000000000 : ℝ), (157941437/250000000 : ℝ)] ![(3556429014357/12500000000000 : ℝ), (16550606702827/100000000000000 : ℝ), (54997961161351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(761585517/2000000000 : ℝ)|^69 ≤ (3556429014357/12500000000000 : ℝ)^53
        have hw : |(761585517/2000000000 : ℝ)|=(761585517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2511646513/10000000000 : ℝ)|^69 ≤ (16550606702827/100000000000000 : ℝ)^53
        have hw : |(-2511646513/10000000000 : ℝ)|=(2511646513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157941437/250000000 : ℝ)|^69 ≤ (54997961161351/100000000000000 : ℝ)^53
        have hw : |(157941437/250000000 : ℝ)|=(157941437/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308075_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((56589/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(56589/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3113/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3113/4000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29201/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29201/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16887/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16887/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-8351/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-8351/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5637/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5637/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s2_pow0 : (56589/100000 : ℝ) ^ (17/4 : ℝ) ≤ (4447142922583754121/50000000000000000000 : ℝ) := by
    have hpowers : (56589/100000 : ℝ)^17 ≤ (4447142922583754121/50000000000000000000 : ℝ)^4 := by
      have hnat : (56589 : ℕ)^17*50000000000000000000^4 ≤ 4447142922583754121^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56589 100000 4447142922583754121 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (56589/100000 : ℝ)) (X := (4447142922583754121/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (54447142922583754121/50000000000000000000 : ℝ) ≤ (2550627800260823/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (54447142922583754121/50000000000000000000 : ℝ)^4 ≤ (2550627800260823/2500000000000000 : ℝ)^17 := by
      have hnat : (54447142922583754121 : ℕ)^4*2500000000000000^17 ≤ 2550627800260823^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54447142922583754121 50000000000000000000 2550627800260823 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2550627800260823/2500000000000000 : ℝ)) (X := (54447142922583754121/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (29447142922583754121/25000000000000000000 : ℝ) ≤ (10392742196048329/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (29447142922583754121/25000000000000000000 : ℝ)^4 ≤ (10392742196048329/10000000000000000 : ℝ)^17 := by
      have hnat : (29447142922583754121 : ℕ)^4*10000000000000000^17 ≤ 10392742196048329^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29447142922583754121 25000000000000000000 10392742196048329 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10392742196048329/10000000000000000 : ℝ)) (X := (29447142922583754121/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(50627800260823/1414725000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(190230995005037/5658900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (56589/100000 : ℝ)) (alpha := (50627800260823/1414725000000000 : ℝ)) (beta := (190230995005037/5658900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (56589/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(50627800260823/1414725000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(190230995005037/5658900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (3113/4000 : ℝ) ^ (17/4 : ℝ) ≤ (17227660477014049273/50000000000000000000 : ℝ) := by
    have hpowers : (3113/4000 : ℝ)^17 ≤ (17227660477014049273/50000000000000000000 : ℝ)^4 := by
      have hnat : (3113 : ℕ)^17*50000000000000000000^4 ≤ 17227660477014049273^4*4000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3113 4000 17227660477014049273 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3113/4000 : ℝ)) (X := (17227660477014049273/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (67227660477014049273/50000000000000000000 : ℝ) ≤ (10721452987364043/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (67227660477014049273/50000000000000000000 : ℝ)^4 ≤ (10721452987364043/10000000000000000 : ℝ)^17 := by
      have hnat : (67227660477014049273 : ℕ)^4*10000000000000000^17 ≤ 10721452987364043^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67227660477014049273 50000000000000000000 10721452987364043 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10721452987364043/10000000000000000 : ℝ)) (X := (67227660477014049273/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (42227660477014049273/25000000000000000000 : ℝ) ≤ (11312702229001243/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (42227660477014049273/25000000000000000000 : ℝ)^4 ≤ (11312702229001243/10000000000000000 : ℝ)^17 := by
      have hnat : (42227660477014049273 : ℕ)^4*10000000000000000^17 ≤ 11312702229001243^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42227660477014049273 25000000000000000000 11312702229001243 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11312702229001243/10000000000000000 : ℝ)) (X := (42227660477014049273/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(65586635214913/707500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1478123104093/19456250000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (3113/4000 : ℝ)) (alpha := (65586635214913/707500000000000 : ℝ)) (beta := (1478123104093/19456250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (3113/4000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(65586635214913/707500000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1478123104093/19456250000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (29201/50000 : ℝ) ^ (17/4 : ℝ) ≤ (508496319859746603/5000000000000000000 : ℝ) := by
    have hpowers : (29201/50000 : ℝ)^17 ≤ (508496319859746603/5000000000000000000 : ℝ)^4 := by
      have hnat : (29201 : ℕ)^17*5000000000000000000^4 ≤ 508496319859746603^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29201 50000 508496319859746603 5000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29201/50000 : ℝ)) (X := (508496319859746603/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (5508496319859746603/5000000000000000000 : ℝ) ≤ (2557626947617381/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (5508496319859746603/5000000000000000000 : ℝ)^4 ≤ (2557626947617381/2500000000000000 : ℝ)^17 := by
      have hnat : (5508496319859746603 : ℕ)^4*2500000000000000^17 ≤ 2557626947617381^17*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5508496319859746603 5000000000000000000 2557626947617381 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2557626947617381/2500000000000000 : ℝ)) (X := (5508496319859746603/5000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (3008496319859746603/2500000000000000000 : ℝ) ≤ (2611318739446219/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3008496319859746603/2500000000000000000 : ℝ)^4 ≤ (2611318739446219/2500000000000000 : ℝ)^17 := by
      have hnat : (3008496319859746603 : ℕ)^4*2500000000000000^17 ≤ 2611318739446219^17*2500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3008496319859746603 2500000000000000000 2611318739446219 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2611318739446219/2500000000000000 : ℝ)) (X := (3008496319859746603/2500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(57626947617381/1460050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(26845895914419/730025000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (29201/50000 : ℝ)) (alpha := (57626947617381/1460050000000000 : ℝ)) (beta := (26845895914419/730025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29201/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(57626947617381/1460050000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(26845895914419/730025000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-768620699/5000000000 : ℝ)*X 0 0+(-2939652729/5000000000 : ℝ)*X 0 1+(5058917331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2574828869/5000000000 : ℝ)*X 2 0+(-2040175763/5000000000 : ℝ)*X 2 1+(-3628990161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3457447447/10000000000 : ℝ)*X 0 0+(-2923506731/10000000000 : ℝ)*X 0 1+(3147491703/5000000000 : ℝ)*X 0 2+(3457447447/10000000000 : ℝ)*X 1 0+(-2923506731/10000000000 : ℝ)*X 1 1+(3147491703/5000000000 : ℝ)*X 1 2+(3457447447/10000000000 : ℝ)*X 2 0+(-2923506731/10000000000 : ℝ)*X 2 1+(3147491703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-17043139/125000000 : ℝ)*X 0 0+(-6565825963/10000000000 : ℝ)*X 0 1+(887083841/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((6313862671/10000000000 : ℝ)*X 1 0+(818119521/2500000000 : ℝ)*X 1 1+(3091250351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((5377023727/10000000000 : ℝ)*X 2 0+(-486182271/1250000000 : ℝ)*X 2 1+(-714167389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2528207379/10000000000 : ℝ)*X 0 0+(-127758591/625000000 : ℝ)*X 0 1+(191441981/250000000 : ℝ)*X 0 2+(2528207379/10000000000 : ℝ)*X 1 0+(-127758591/625000000 : ℝ)*X 1 1+(191441981/250000000 : ℝ)*X 1 2+(2528207379/10000000000 : ℝ)*X 2 0+(-127758591/625000000 : ℝ)*X 2 1+(191441981/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1041474153/10000000000 : ℝ)*X 0 0+(-1436586317/2500000000 : ℝ)*X 0 1+(5519087173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((685914481/1000000000 : ℝ)*X 1 0+(3113183557/10000000000 : ℝ)*X 1 1+(159510193/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1103410377/2000000000 : ℝ)*X 2 0+(-4133732497/10000000000 : ℝ)*X 2 1+(-3151108341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1352968887/5000000000 : ℝ)*X 0 0+(-1122324447/5000000000 : ℝ)*X 0 1+(1478243289/2000000000 : ℝ)*X 0 2+(1352968887/5000000000 : ℝ)*X 1 0+(-1122324447/5000000000 : ℝ)*X 1 1+(1478243289/2000000000 : ℝ)*X 1 2+(1352968887/5000000000 : ℝ)*X 2 0+(-1122324447/5000000000 : ℝ)*X 2 1+(1478243289/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1008753141/10000000000 : ℝ)*X 0 0+(-804494289/1250000000 : ℝ)*X 0 1+(4814392937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1738063381/2500000000 : ℝ)*X 1 0+(2888956231/10000000000 : ℝ)*X 1 1+(2661177133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4940321581/10000000000 : ℝ)*X 2 0+(-130743669/312500000 : ℝ)*X 2 1+(-3752007951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((761585517/2000000000 : ℝ)*X 0 0+(-2511646513/10000000000 : ℝ)*X 0 1+(157941437/250000000 : ℝ)*X 0 2+(761585517/2000000000 : ℝ)*X 1 0+(-2511646513/10000000000 : ℝ)*X 1 1+(157941437/250000000 : ℝ)*X 1 2+(761585517/2000000000 : ℝ)*X 2 0+(-2511646513/10000000000 : ℝ)*X 2 1+(157941437/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308075_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((16887/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16887/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37069380108735419181878716135243/2143372344148750000000000000000000000 : ℝ) := by norm_num
    linear_combination (688370574959/1000000000000 : ℝ)*(base40) + (1458829/250000000000 : ℝ)*(base49) + (67445193733/1000000000000 : ℝ)*(base60) + (1388126299379/250000000000 : ℝ)*(major_s2_0) + (1388126299379/250000000000 : ℝ)*(major_s2_1) + (1388126299379/250000000000 : ℝ)*(major_s2_2) + (23879369/500000000000 : ℝ)*(sp_s2_0) + (541726019/1000000000000 : ℝ)*(sp_s2_2) + (3780899656691/500000000000 : ℝ)*(sp_s2_7) + (756185501229/100000000000 : ℝ)*(sp_s2_8) + (7561306498047/1000000000000 : ℝ)*(sp_s2_9) + (1771574808889/500000000000 : ℝ)*(sp_s2_13) + (794017/100000000000 : ℝ)*(sp_s2_21) + (53033/7812500000 : ℝ)*(sp_s2_23) + (1771574808889/500000000000 : ℝ)*(f.failure) + (756185501229/100000000000 : ℝ)*(f.sum) + (56463679476295081/1136283912500000000000000000000 : ℝ)*base63 + (98302740052509/730025000000000000000000000 : ℝ)*base64 + (208108587201/88437500000000000000000000 : ℝ)*base67 + (9668519802333/182506250000000000000000000 : ℝ)*base68 + (4326878576662378277/10327846181250000000000000000000 : ℝ)*base70 + (16915171460189/44210156250000000000000000 : ℝ)*base73 + (29926244689791/155650000000000000000000000 : ℝ)*base75 + (575523777358207/1414725000000000000000000000 : ℝ)*base76 + (3155434147799504503/10009179375000000000000000000000 : ℝ)*base79 + (4079/50000000000000000 : ℝ)*base87 + (4079/50000000000000000 : ℝ)*base89 + (4079/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-8351/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-8351/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1391862297723927704243480545043/133960771509296875000000000000000000 : ℝ) := by norm_num
    linear_combination (3158361/500000000000 : ℝ)*(base13) + (820937202361/500000000000 : ℝ)*(base40) + (768883/200000000000 : ℝ)*(base49) + (515674329963/1000000000000 : ℝ)*(base60) + (7658188268431/1000000000000 : ℝ)*(major_s2_0) + (7658188268431/1000000000000 : ℝ)*(major_s2_1) + (7658188268431/1000000000000 : ℝ)*(major_s2_2) + (44142029/500000000000 : ℝ)*(sp_s2_0) + (90145523/1000000000000 : ℝ)*(sp_s2_13) + (10429456061763/1000000000000 : ℝ)*(sp_s2_14) + (10429239613229/1000000000000 : ℝ)*(sp_s2_15) + (10429550662543/1000000000000 : ℝ)*(sp_s2_16) + (4886732265431/1000000000000 : ℝ)*(sp_s2_20) + (155524657/500000000000 : ℝ)*(sp_s2_22) + (977364482191/200000000000 : ℝ)*(f.failure) + (10429550662543/1000000000000 : ℝ)*(f.sum) + (806408006608413159/4545135650000000000000000000000 : ℝ)*base63 + (2558180139601/11406640625000000000000000 : ℝ)*base64 + (375339484587503/707500000000000000000000000 : ℝ)*base67 + (174737532801513/730025000000000000000000000 : ℝ)*base69 + (45813760880540872541/82622769450000000000000000000000 : ℝ)*base70 + (5155372220628137/5658900000000000000000000000 : ℝ)*base73 + (24746575689273/77825000000000000000000000 : ℝ)*base75 + (1806106003980589/2829450000000000000000000000 : ℝ)*base76 + (7953177158071171823/10009179375000000000000000000000 : ℝ)*base79 + (13801/20000000000000000 : ℝ)*base87 + (13801/20000000000000000 : ℝ)*base89 + (13801/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5637/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5637/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (91607159372342609655473628799/17146978753190000000000000000000000 : ℝ) := by norm_num
    linear_combination (1557555201477/1000000000000 : ℝ)*(base40) + (10941315863/200000000000 : ℝ)*(base49) + (665175980377/100000000000 : ℝ)*(major_s2_0) + (665175980377/100000000000 : ℝ)*(major_s2_1) + (665175980377/100000000000 : ℝ)*(major_s2_2) + (3425903/100000000000 : ℝ)*(sp_s2_0) + (48043419/1000000000000 : ℝ)*(sp_s2_6) + (6967807/125000000000 : ℝ)*(sp_s2_7) + (10234509/200000000000 : ℝ)*(sp_s2_15) + (2252949/250000000000 : ℝ)*(sp_s2_16) + (1132353103437/125000000000 : ℝ)*(sp_s2_21) + (2264715914109/250000000000 : ℝ)*(sp_s2_22) + (4529452908593/500000000000 : ℝ)*(sp_s2_23) + (4244554954309/1000000000000 : ℝ)*(sp_s2_27) + (4244602997729/1000000000000 : ℝ)*(f.failure) + (4529457414491/500000000000 : ℝ)*(f.sum) + (28637284451837069/45451356500000000000000000000 : ℝ)*base63 + (65048960738387/146005000000000000000000000 : ℝ)*base65 + (12983191804499/70750000000000000000000000 : ℝ)*base66 + (43980290372951/146005000000000000000000000 : ℝ)*base69 + (6893430370323299719/16524553890000000000000000000000 : ℝ)*base70 + (356608853654951/565890000000000000000000000 : ℝ)*base73 + (92776741251/972812500000000000000000 : ℝ)*base75 + (42389099939341/282945000000000000000000000 : ℝ)*base76 + (891866552237345741/1000917937500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (109319/100000000000000000 : ℝ)*base87 + (109319/100000000000000000 : ℝ)*base89 + (109319/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((56589/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(56589/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3113/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3113/4000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29201/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29201/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16887/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16887/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-8351/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-8351/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5637/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5637/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308075_s2 p hpa hpb X hX hprev1

#print axioms solution

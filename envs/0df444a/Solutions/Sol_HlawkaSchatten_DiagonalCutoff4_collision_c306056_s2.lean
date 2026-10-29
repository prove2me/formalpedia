-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306056_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:56:18.520469+00:00
-- url     : https://prove2.me/submissions/d628e2e8-e042-4a62-839b-f2b578b7961c

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
theorem collision_support_c306056_s2_s2_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3412129869/10000000000 : ℝ)*x 0 + (-853032487/2500000000 : ℝ)*x 1 + (-374678457/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3412129869/10000000000 : ℝ)^135 ≤ (6107818472897/25000000000000 : ℝ)^103 := by
    have hnat : (3412129869 : ℕ)^135*25000000000000^103 ≤ 6107818472897^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3412129869 10000000000 6107818472897 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (853032487/2500000000 : ℝ)^135 ≤ (12215637316487/50000000000000 : ℝ)^103 := by
    have hnat : (853032487 : ℕ)^135*50000000000000^103 ≤ 12215637316487^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853032487 2500000000 12215637316487 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374678457/625000000 : ℝ)^135 ≤ (12784362865711/25000000000000 : ℝ)^103 := by
    have hnat : (374678457 : ℕ)^135*25000000000000^103 ≤ 12784362865711^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374678457 625000000 12784362865711 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3412129869/10000000000 : ℝ), (-853032487/2500000000 : ℝ), (-374678457/625000000 : ℝ)] ![(6107818472897/25000000000000 : ℝ), (12215637316487/50000000000000 : ℝ), (12784362865711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3412129869/10000000000 : ℝ)|^135 ≤ (6107818472897/25000000000000 : ℝ)^103
        have hw : |(3412129869/10000000000 : ℝ)|=(3412129869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-853032487/2500000000 : ℝ)|^135 ≤ (12215637316487/50000000000000 : ℝ)^103
        have hw : |(-853032487/2500000000 : ℝ)|=(853032487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-374678457/625000000 : ℝ)|^135 ≤ (12784362865711/25000000000000 : ℝ)^103
        have hw : |(-374678457/625000000 : ℝ)|=(374678457/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1075987631/2000000000 : ℝ)*x 0 + (5379938373/10000000000 : ℝ)*x 1 + (472088113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075987631/2000000000 : ℝ)^135 ≤ (44374684081923/100000000000000 : ℝ)^103 := by
    have hnat : (1075987631 : ℕ)^135*100000000000000^103 ≤ 44374684081923^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075987631 2000000000 44374684081923 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5379938373/10000000000 : ℝ)^135 ≤ (44374686438659/100000000000000 : ℝ)^103 := by
    have hnat : (5379938373 : ℕ)^135*100000000000000^103 ≤ 44374686438659^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379938373 10000000000 44374686438659 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472088113/2500000000 : ℝ)^135 ≤ (2812657366607/25000000000000 : ℝ)^103 := by
    have hnat : (472088113 : ℕ)^135*25000000000000^103 ≤ 2812657366607^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472088113 2500000000 2812657366607 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075987631/2000000000 : ℝ), (5379938373/10000000000 : ℝ), (472088113/2500000000 : ℝ)] ![(44374684081923/100000000000000 : ℝ), (44374686438659/100000000000000 : ℝ), (2812657366607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075987631/2000000000 : ℝ)|^135 ≤ (44374684081923/100000000000000 : ℝ)^103
        have hw : |(1075987631/2000000000 : ℝ)|=(1075987631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5379938373/10000000000 : ℝ)|^135 ≤ (44374686438659/100000000000000 : ℝ)^103
        have hw : |(5379938373/10000000000 : ℝ)|=(5379938373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(472088113/2500000000 : ℝ)|^135 ≤ (2812657366607/25000000000000 : ℝ)^103
        have hw : |(472088113/2500000000 : ℝ)|=(472088113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1663825739/5000000000 : ℝ)*x 0 + (626586129/2000000000 : ℝ)*x 1 + (-3147254259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1663825739/5000000000 : ℝ)^135 ≤ (11820771064277/50000000000000 : ℝ)^103 := by
    have hnat : (1663825739 : ℕ)^135*50000000000000^103 ≤ 11820771064277^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663825739 5000000000 11820771064277 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626586129/2000000000 : ℝ)^135 ≤ (21845046080789/100000000000000 : ℝ)^103 := by
    have hnat : (626586129 : ℕ)^135*100000000000000^103 ≤ 21845046080789^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626586129 2000000000 21845046080789 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3147254259/5000000000 : ℝ)^135 ≤ (27256705888247/50000000000000 : ℝ)^103 := by
    have hnat : (3147254259 : ℕ)^135*50000000000000^103 ≤ 27256705888247^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3147254259 5000000000 27256705888247 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1663825739/5000000000 : ℝ), (626586129/2000000000 : ℝ), (-3147254259/5000000000 : ℝ)] ![(11820771064277/50000000000000 : ℝ), (21845046080789/100000000000000 : ℝ), (27256705888247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1663825739/5000000000 : ℝ)|^135 ≤ (11820771064277/50000000000000 : ℝ)^103
        have hw : |(-1663825739/5000000000 : ℝ)|=(1663825739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626586129/2000000000 : ℝ)|^135 ≤ (21845046080789/100000000000000 : ℝ)^103
        have hw : |(626586129/2000000000 : ℝ)|=(626586129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3147254259/5000000000 : ℝ)|^135 ≤ (27256705888247/50000000000000 : ℝ)^103
        have hw : |(-3147254259/5000000000 : ℝ)|=(3147254259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1663825739/5000000000 : ℝ)*x 0 + (-626586129/2000000000 : ℝ)*x 1 + (-3147254259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1663825739/5000000000 : ℝ)^135 ≤ (11820771064277/50000000000000 : ℝ)^103 := by
    have hnat : (1663825739 : ℕ)^135*50000000000000^103 ≤ 11820771064277^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663825739 5000000000 11820771064277 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626586129/2000000000 : ℝ)^135 ≤ (21845046080789/100000000000000 : ℝ)^103 := by
    have hnat : (626586129 : ℕ)^135*100000000000000^103 ≤ 21845046080789^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626586129 2000000000 21845046080789 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3147254259/5000000000 : ℝ)^135 ≤ (27256705888247/50000000000000 : ℝ)^103 := by
    have hnat : (3147254259 : ℕ)^135*50000000000000^103 ≤ 27256705888247^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3147254259 5000000000 27256705888247 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1663825739/5000000000 : ℝ), (-626586129/2000000000 : ℝ), (-3147254259/5000000000 : ℝ)] ![(11820771064277/50000000000000 : ℝ), (21845046080789/100000000000000 : ℝ), (27256705888247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1663825739/5000000000 : ℝ)|^135 ≤ (11820771064277/50000000000000 : ℝ)^103
        have hw : |(1663825739/5000000000 : ℝ)|=(1663825739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-626586129/2000000000 : ℝ)|^135 ≤ (21845046080789/100000000000000 : ℝ)^103
        have hw : |(-626586129/2000000000 : ℝ)|=(626586129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3147254259/5000000000 : ℝ)|^135 ≤ (27256705888247/50000000000000 : ℝ)^103
        have hw : |(-3147254259/5000000000 : ℝ)|=(3147254259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (329045687/625000000 : ℝ)*x 0 + (5766055103/10000000000 : ℝ)*x 1 + (373348841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329045687/625000000 : ℝ)^135 ≤ (8626675110701/20000000000000 : ℝ)^103 := by
    have hnat : (329045687 : ℕ)^135*20000000000000^103 ≤ 8626675110701^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329045687 625000000 8626675110701 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5766055103/10000000000 : ℝ)^135 ≤ (48594677383521/100000000000000 : ℝ)^103 := by
    have hnat : (5766055103 : ℕ)^135*100000000000000^103 ≤ 48594677383521^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5766055103 10000000000 48594677383521 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373348841/2500000000 : ℝ)^135 ≤ (1654389410857/20000000000000 : ℝ)^103 := by
    have hnat : (373348841 : ℕ)^135*20000000000000^103 ≤ 1654389410857^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373348841 2500000000 1654389410857 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329045687/625000000 : ℝ), (5766055103/10000000000 : ℝ), (373348841/2500000000 : ℝ)] ![(8626675110701/20000000000000 : ℝ), (48594677383521/100000000000000 : ℝ), (1654389410857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329045687/625000000 : ℝ)|^135 ≤ (8626675110701/20000000000000 : ℝ)^103
        have hw : |(329045687/625000000 : ℝ)|=(329045687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5766055103/10000000000 : ℝ)|^135 ≤ (48594677383521/100000000000000 : ℝ)^103
        have hw : |(5766055103/10000000000 : ℝ)|=(5766055103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(373348841/2500000000 : ℝ)|^135 ≤ (1654389410857/20000000000000 : ℝ)^103
        have hw : |(373348841/2500000000 : ℝ)|=(373348841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_12 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (329045687/625000000 : ℝ)*x 0 + (5766055103/10000000000 : ℝ)*x 1 + (-373348841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329045687/625000000 : ℝ)^135 ≤ (8626675110701/20000000000000 : ℝ)^103 := by
    have hnat : (329045687 : ℕ)^135*20000000000000^103 ≤ 8626675110701^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329045687 625000000 8626675110701 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5766055103/10000000000 : ℝ)^135 ≤ (48594677383521/100000000000000 : ℝ)^103 := by
    have hnat : (5766055103 : ℕ)^135*100000000000000^103 ≤ 48594677383521^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5766055103 10000000000 48594677383521 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373348841/2500000000 : ℝ)^135 ≤ (1654389410857/20000000000000 : ℝ)^103 := by
    have hnat : (373348841 : ℕ)^135*20000000000000^103 ≤ 1654389410857^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373348841 2500000000 1654389410857 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329045687/625000000 : ℝ), (5766055103/10000000000 : ℝ), (-373348841/2500000000 : ℝ)] ![(8626675110701/20000000000000 : ℝ), (48594677383521/100000000000000 : ℝ), (1654389410857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329045687/625000000 : ℝ)|^135 ≤ (8626675110701/20000000000000 : ℝ)^103
        have hw : |(329045687/625000000 : ℝ)|=(329045687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5766055103/10000000000 : ℝ)|^135 ≤ (48594677383521/100000000000000 : ℝ)^103
        have hw : |(5766055103/10000000000 : ℝ)|=(5766055103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-373348841/2500000000 : ℝ)|^135 ≤ (1654389410857/20000000000000 : ℝ)^103
        have hw : |(-373348841/2500000000 : ℝ)|=(373348841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-156646533/500000000 : ℝ)*x 0 + (3327651471/10000000000 : ℝ)*x 1 + (-6294508511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156646533/500000000 : ℝ)^135 ≤ (10922523108937/50000000000000 : ℝ)^103 := by
    have hnat : (156646533 : ℕ)^135*50000000000000^103 ≤ 10922523108937^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156646533 500000000 10922523108937 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3327651471/10000000000 : ℝ)^135 ≤ (23641542063371/100000000000000 : ℝ)^103 := by
    have hnat : (3327651471 : ℕ)^135*100000000000000^103 ≤ 23641542063371^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3327651471 10000000000 23641542063371 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6294508511/10000000000 : ℝ)^135 ≤ (13628352924259/25000000000000 : ℝ)^103 := by
    have hnat : (6294508511 : ℕ)^135*25000000000000^103 ≤ 13628352924259^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6294508511 10000000000 13628352924259 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-156646533/500000000 : ℝ), (3327651471/10000000000 : ℝ), (-6294508511/10000000000 : ℝ)] ![(10922523108937/50000000000000 : ℝ), (23641542063371/100000000000000 : ℝ), (13628352924259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-156646533/500000000 : ℝ)|^135 ≤ (10922523108937/50000000000000 : ℝ)^103
        have hw : |(-156646533/500000000 : ℝ)|=(156646533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3327651471/10000000000 : ℝ)|^135 ≤ (23641542063371/100000000000000 : ℝ)^103
        have hw : |(3327651471/10000000000 : ℝ)|=(3327651471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6294508511/10000000000 : ℝ)|^135 ≤ (13628352924259/25000000000000 : ℝ)^103
        have hw : |(-6294508511/10000000000 : ℝ)|=(6294508511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (156646533/500000000 : ℝ)*x 0 + (-3327651471/10000000000 : ℝ)*x 1 + (-6294508511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156646533/500000000 : ℝ)^135 ≤ (10922523108937/50000000000000 : ℝ)^103 := by
    have hnat : (156646533 : ℕ)^135*50000000000000^103 ≤ 10922523108937^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156646533 500000000 10922523108937 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3327651471/10000000000 : ℝ)^135 ≤ (23641542063371/100000000000000 : ℝ)^103 := by
    have hnat : (3327651471 : ℕ)^135*100000000000000^103 ≤ 23641542063371^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3327651471 10000000000 23641542063371 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6294508511/10000000000 : ℝ)^135 ≤ (13628352924259/25000000000000 : ℝ)^103 := by
    have hnat : (6294508511 : ℕ)^135*25000000000000^103 ≤ 13628352924259^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6294508511 10000000000 13628352924259 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(156646533/500000000 : ℝ), (-3327651471/10000000000 : ℝ), (-6294508511/10000000000 : ℝ)] ![(10922523108937/50000000000000 : ℝ), (23641542063371/100000000000000 : ℝ), (13628352924259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(156646533/500000000 : ℝ)|^135 ≤ (10922523108937/50000000000000 : ℝ)^103
        have hw : |(156646533/500000000 : ℝ)|=(156646533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3327651471/10000000000 : ℝ)|^135 ≤ (23641542063371/100000000000000 : ℝ)^103
        have hw : |(-3327651471/10000000000 : ℝ)|=(3327651471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6294508511/10000000000 : ℝ)|^135 ≤ (13628352924259/25000000000000 : ℝ)^103
        have hw : |(-6294508511/10000000000 : ℝ)|=(6294508511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2883027539/5000000000 : ℝ)*x 0 + (5264731031/10000000000 : ℝ)*x 1 + (1493395343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2883027539/5000000000 : ℝ)^135 ≤ (4859467710737/10000000000000 : ℝ)^103 := by
    have hnat : (2883027539 : ℕ)^135*10000000000000^103 ≤ 4859467710737^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2883027539 5000000000 4859467710737 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264731031/10000000000 : ℝ)^135 ≤ (43133375972297/100000000000000 : ℝ)^103 := by
    have hnat : (5264731031 : ℕ)^135*100000000000000^103 ≤ 43133375972297^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264731031 10000000000 43133375972297 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1493395343/10000000000 : ℝ)^135 ≤ (8271946901827/100000000000000 : ℝ)^103 := by
    have hnat : (1493395343 : ℕ)^135*100000000000000^103 ≤ 8271946901827^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493395343 10000000000 8271946901827 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2883027539/5000000000 : ℝ), (5264731031/10000000000 : ℝ), (1493395343/10000000000 : ℝ)] ![(4859467710737/10000000000000 : ℝ), (43133375972297/100000000000000 : ℝ), (8271946901827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2883027539/5000000000 : ℝ)|^135 ≤ (4859467710737/10000000000000 : ℝ)^103
        have hw : |(2883027539/5000000000 : ℝ)|=(2883027539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264731031/10000000000 : ℝ)|^135 ≤ (43133375972297/100000000000000 : ℝ)^103
        have hw : |(5264731031/10000000000 : ℝ)|=(5264731031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1493395343/10000000000 : ℝ)|^135 ≤ (8271946901827/100000000000000 : ℝ)^103
        have hw : |(1493395343/10000000000 : ℝ)|=(1493395343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_18 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2883027539/5000000000 : ℝ)*x 0 + (5264731031/10000000000 : ℝ)*x 1 + (-1493395343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2883027539/5000000000 : ℝ)^135 ≤ (4859467710737/10000000000000 : ℝ)^103 := by
    have hnat : (2883027539 : ℕ)^135*10000000000000^103 ≤ 4859467710737^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2883027539 5000000000 4859467710737 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264731031/10000000000 : ℝ)^135 ≤ (43133375972297/100000000000000 : ℝ)^103 := by
    have hnat : (5264731031 : ℕ)^135*100000000000000^103 ≤ 43133375972297^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264731031 10000000000 43133375972297 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1493395343/10000000000 : ℝ)^135 ≤ (8271946901827/100000000000000 : ℝ)^103 := by
    have hnat : (1493395343 : ℕ)^135*100000000000000^103 ≤ 8271946901827^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493395343 10000000000 8271946901827 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2883027539/5000000000 : ℝ), (5264731031/10000000000 : ℝ), (-1493395343/10000000000 : ℝ)] ![(4859467710737/10000000000000 : ℝ), (43133375972297/100000000000000 : ℝ), (8271946901827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2883027539/5000000000 : ℝ)|^135 ≤ (4859467710737/10000000000000 : ℝ)^103
        have hw : |(2883027539/5000000000 : ℝ)|=(2883027539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264731031/10000000000 : ℝ)|^135 ≤ (43133375972297/100000000000000 : ℝ)^103
        have hw : |(5264731031/10000000000 : ℝ)|=(5264731031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1493395343/10000000000 : ℝ)|^135 ≤ (8271946901827/100000000000000 : ℝ)^103
        have hw : |(-1493395343/10000000000 : ℝ)|=(1493395343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_19 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1734353343/5000000000 : ℝ)*x 0 + (3398623621/10000000000 : ℝ)*x 1 + (-2979269809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1734353343/5000000000 : ℝ)^135 ≤ (12481794362417/50000000000000 : ℝ)^103 := by
    have hnat : (1734353343 : ℕ)^135*50000000000000^103 ≤ 12481794362417^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1734353343 5000000000 12481794362417 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3398623621/10000000000 : ℝ)^135 ≤ (24304600774303/100000000000000 : ℝ)^103 := by
    have hnat : (3398623621 : ℕ)^135*100000000000000^103 ≤ 24304600774303^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3398623621 10000000000 24304600774303 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2979269809/5000000000 : ℝ)^135 ≤ (12682952620591/25000000000000 : ℝ)^103 := by
    have hnat : (2979269809 : ℕ)^135*25000000000000^103 ≤ 12682952620591^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979269809 5000000000 12682952620591 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1734353343/5000000000 : ℝ), (3398623621/10000000000 : ℝ), (-2979269809/5000000000 : ℝ)] ![(12481794362417/50000000000000 : ℝ), (24304600774303/100000000000000 : ℝ), (12682952620591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1734353343/5000000000 : ℝ)|^135 ≤ (12481794362417/50000000000000 : ℝ)^103
        have hw : |(-1734353343/5000000000 : ℝ)|=(1734353343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3398623621/10000000000 : ℝ)|^135 ≤ (24304600774303/100000000000000 : ℝ)^103
        have hw : |(3398623621/10000000000 : ℝ)|=(3398623621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2979269809/5000000000 : ℝ)|^135 ≤ (12682952620591/25000000000000 : ℝ)^103
        have hw : |(-2979269809/5000000000 : ℝ)|=(2979269809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3362833113/10000000000 : ℝ)*x 0 + (-3432916241/10000000000 : ℝ)*x 1 + (-3009331087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3362833113/10000000000 : ℝ)^135 ≤ (5992420967533/25000000000000 : ℝ)^103 := by
    have hnat : (3362833113 : ℕ)^135*25000000000000^103 ≤ 5992420967533^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3362833113 10000000000 5992420967533 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3432916241/10000000000 : ℝ)^135 ≤ (24626530621237/100000000000000 : ℝ)^103 := by
    have hnat : (3432916241 : ℕ)^135*100000000000000^103 ≤ 24626530621237^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3432916241 10000000000 24626530621237 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3009331087/5000000000 : ℝ)^135 ≤ (12850946372713/25000000000000 : ℝ)^103 := by
    have hnat : (3009331087 : ℕ)^135*25000000000000^103 ≤ 12850946372713^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3009331087 5000000000 12850946372713 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3362833113/10000000000 : ℝ), (-3432916241/10000000000 : ℝ), (-3009331087/5000000000 : ℝ)] ![(5992420967533/25000000000000 : ℝ), (24626530621237/100000000000000 : ℝ), (12850946372713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3362833113/10000000000 : ℝ)|^135 ≤ (5992420967533/25000000000000 : ℝ)^103
        have hw : |(3362833113/10000000000 : ℝ)|=(3362833113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3432916241/10000000000 : ℝ)|^135 ≤ (24626530621237/100000000000000 : ℝ)^103
        have hw : |(-3432916241/10000000000 : ℝ)|=(3432916241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3009331087/5000000000 : ℝ)|^135 ≤ (12850946372713/25000000000000 : ℝ)^103
        have hw : |(-3009331087/5000000000 : ℝ)|=(3009331087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5383816873/10000000000 : ℝ)*x 0 + (5383816911/10000000000 : ℝ)*x 1 + (1877602519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383816873/10000000000 : ℝ)^135 ≤ (44416620503337/100000000000000 : ℝ)^103 := by
    have hnat : (5383816873 : ℕ)^135*100000000000000^103 ≤ 44416620503337^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383816873 10000000000 44416620503337 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5383816911/10000000000 : ℝ)^135 ≤ (11104155228559/25000000000000 : ℝ)^103 := by
    have hnat : (5383816911 : ℕ)^135*25000000000000^103 ≤ 11104155228559^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383816911 10000000000 11104155228559 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877602519/10000000000 : ℝ)^135 ≤ (697922409951/6250000000000 : ℝ)^103 := by
    have hnat : (1877602519 : ℕ)^135*6250000000000^103 ≤ 697922409951^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877602519 10000000000 697922409951 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383816873/10000000000 : ℝ), (5383816911/10000000000 : ℝ), (1877602519/10000000000 : ℝ)] ![(44416620503337/100000000000000 : ℝ), (11104155228559/25000000000000 : ℝ), (697922409951/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383816873/10000000000 : ℝ)|^135 ≤ (44416620503337/100000000000000 : ℝ)^103
        have hw : |(5383816873/10000000000 : ℝ)|=(5383816873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5383816911/10000000000 : ℝ)|^135 ≤ (11104155228559/25000000000000 : ℝ)^103
        have hw : |(5383816911/10000000000 : ℝ)|=(5383816911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1877602519/10000000000 : ℝ)|^135 ≤ (697922409951/6250000000000 : ℝ)^103
        have hw : |(1877602519/10000000000 : ℝ)|=(1877602519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306056_s2_s2_25 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1327288303/2500000000 : ℝ)*x 0 + (5443249961/10000000000 : ℝ)*x 1 + (-379665951/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327288303/2500000000 : ℝ)^135 ≤ (43611016804653/100000000000000 : ℝ)^103 := by
    have hnat : (1327288303 : ℕ)^135*100000000000000^103 ≤ 43611016804653^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327288303 2500000000 43611016804653 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443249961/10000000000 : ℝ)^135 ≤ (45060377997323/100000000000000 : ℝ)^103 := by
    have hnat : (5443249961 : ℕ)^135*100000000000000^103 ≤ 45060377997323^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443249961 10000000000 45060377997323 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379665951/2000000000 : ℝ)^135 ≤ (1416075647137/12500000000000 : ℝ)^103 := by
    have hnat : (379665951 : ℕ)^135*12500000000000^103 ≤ 1416075647137^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379665951 2000000000 1416075647137 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327288303/2500000000 : ℝ), (5443249961/10000000000 : ℝ), (-379665951/2000000000 : ℝ)] ![(43611016804653/100000000000000 : ℝ), (45060377997323/100000000000000 : ℝ), (1416075647137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327288303/2500000000 : ℝ)|^135 ≤ (43611016804653/100000000000000 : ℝ)^103
        have hw : |(1327288303/2500000000 : ℝ)|=(1327288303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443249961/10000000000 : ℝ)|^135 ≤ (45060377997323/100000000000000 : ℝ)^103
        have hw : |(5443249961/10000000000 : ℝ)|=(5443249961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-379665951/2000000000 : ℝ)|^135 ≤ (1416075647137/12500000000000 : ℝ)^103
        have hw : |(-379665951/2000000000 : ℝ)|=(379665951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306056_s2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((35999/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35999/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35999/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35999/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-7121/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-7121/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7789/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7789/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7789/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7789/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-67/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-67/12500 : ℝ)*X 1 2) := by
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
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s2_pow0 : (35999/50000 : ℝ) ^ (67/16 : ℝ) ≤ (12632791128649968467/50000000000000000000 : ℝ) := by
    have hpowers : (35999/50000 : ℝ)^67 ≤ (12632791128649968467/50000000000000000000 : ℝ)^16 := by
      have hnat : (35999 : ℕ)^67*50000000000000000000^16 ≤ 12632791128649968467^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35999 50000 12632791128649968467 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35999/50000 : ℝ)) (X := (12632791128649968467/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (62632791128649968467/50000000000000000000 : ℝ) ≤ (2110536194032939/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (62632791128649968467/50000000000000000000 : ℝ)^16 ≤ (2110536194032939/2000000000000000 : ℝ)^67 := by
      have hnat : (62632791128649968467 : ℕ)^16*2000000000000000^67 ≤ 2110536194032939^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62632791128649968467 50000000000000000000 2110536194032939 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2110536194032939/2000000000000000 : ℝ)) (X := (62632791128649968467/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (37632791128649968467/25000000000000000000 : ℝ) ≤ (5513003322496257/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (37632791128649968467/25000000000000000000 : ℝ)^16 ≤ (5513003322496257/5000000000000000 : ℝ)^67 := by
      have hnat : (37632791128649968467 : ℕ)^16*5000000000000000^67 ≤ 5513003322496257^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37632791128649968467 25000000000000000000 5513003322496257 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5513003322496257/5000000000000000 : ℝ)) (X := (37632791128649968467/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(110536194032939/1439960000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(473325674827819/7199800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (35999/50000 : ℝ)) (alpha := (110536194032939/1439960000000000 : ℝ)) (beta := (473325674827819/7199800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (35999/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(110536194032939/1439960000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(473325674827819/7199800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (35999/50000 : ℝ) ^ (67/16 : ℝ) ≤ (12632791128649968467/50000000000000000000 : ℝ) := by
    have hpowers : (35999/50000 : ℝ)^67 ≤ (12632791128649968467/50000000000000000000 : ℝ)^16 := by
      have hnat : (35999 : ℕ)^67*50000000000000000000^16 ≤ 12632791128649968467^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35999 50000 12632791128649968467 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35999/50000 : ℝ)) (X := (12632791128649968467/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (62632791128649968467/50000000000000000000 : ℝ) ≤ (2110536194032939/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (62632791128649968467/50000000000000000000 : ℝ)^16 ≤ (2110536194032939/2000000000000000 : ℝ)^67 := by
      have hnat : (62632791128649968467 : ℕ)^16*2000000000000000^67 ≤ 2110536194032939^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62632791128649968467 50000000000000000000 2110536194032939 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2110536194032939/2000000000000000 : ℝ)) (X := (62632791128649968467/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (37632791128649968467/25000000000000000000 : ℝ) ≤ (5513003322496257/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (37632791128649968467/25000000000000000000 : ℝ)^16 ≤ (5513003322496257/5000000000000000 : ℝ)^67 := by
      have hnat : (37632791128649968467 : ℕ)^16*5000000000000000^67 ≤ 5513003322496257^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37632791128649968467 25000000000000000000 5513003322496257 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5513003322496257/5000000000000000 : ℝ)) (X := (37632791128649968467/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(110536194032939/1439960000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(473325674827819/7199800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (35999/50000 : ℝ)) (alpha := (110536194032939/1439960000000000 : ℝ)) (beta := (473325674827819/7199800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (35999/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(110536194032939/1439960000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(473325674827819/7199800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (7121/100000 : ℝ) ^ (67/16 : ℝ) ≤ (391701637024657/25000000000000000000 : ℝ) := by
    have hpowers : (7121/100000 : ℝ)^67 ≤ (391701637024657/25000000000000000000 : ℝ)^16 := by
      have hnat : (7121 : ℕ)^67*25000000000000000000^16 ≤ 391701637024657^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7121 100000 391701637024657 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7121/100000 : ℝ)) (X := (391701637024657/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (25000391701637024657/25000000000000000000 : ℝ) ≤ (10000037416052657/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25000391701637024657/25000000000000000000 : ℝ)^16 ≤ (10000037416052657/10000000000000000 : ℝ)^67 := by
      have hnat : (25000391701637024657 : ℕ)^16*10000000000000000^67 ≤ 10000037416052657^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000391701637024657 25000000000000000000 10000037416052657 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000037416052657/10000000000000000 : ℝ)) (X := (25000391701637024657/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (12500391701637024657/12500000000000000000 : ℝ) ≤ (5000037415829541/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (12500391701637024657/12500000000000000000 : ℝ)^16 ≤ (5000037415829541/5000000000000000 : ℝ)^67 := by
      have hnat : (12500391701637024657 : ℕ)^16*5000000000000000^67 ≤ 5000037415829541^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500391701637024657 12500000000000000000 5000037415829541 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000037415829541/5000000000000000 : ℝ)) (X := (12500391701637024657/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(37416052657/712100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1496624257/28484000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (7121/100000 : ℝ)) (alpha := (37416052657/712100000000000 : ℝ)) (beta := (1496624257/28484000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (7121/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(37416052657/712100000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1496624257/28484000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((3412129869/10000000000 : ℝ)*X 1 0+(-853032487/2500000000 : ℝ)*X 1 1+(-374678457/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1075987631/2000000000 : ℝ)*X 2 0+(5379938373/10000000000 : ℝ)*X 2 1+(472088113/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1663825739/5000000000 : ℝ)*X 0 0+(626586129/2000000000 : ℝ)*X 0 1+(-3147254259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1663825739/5000000000 : ℝ)*X 1 0+(-626586129/2000000000 : ℝ)*X 1 1+(-3147254259/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((329045687/625000000 : ℝ)*X 2 0+(5766055103/10000000000 : ℝ)*X 2 1+(373348841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((329045687/625000000 : ℝ)*X 0 0+(5766055103/10000000000 : ℝ)*X 0 1+(-373348841/2500000000 : ℝ)*X 0 2+(329045687/625000000 : ℝ)*X 1 0+(5766055103/10000000000 : ℝ)*X 1 1+(-373348841/2500000000 : ℝ)*X 1 2+(329045687/625000000 : ℝ)*X 2 0+(5766055103/10000000000 : ℝ)*X 2 1+(-373348841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-156646533/500000000 : ℝ)*X 0 0+(3327651471/10000000000 : ℝ)*X 0 1+(-6294508511/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((156646533/500000000 : ℝ)*X 1 0+(-3327651471/10000000000 : ℝ)*X 1 1+(-6294508511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2883027539/5000000000 : ℝ)*X 2 0+(5264731031/10000000000 : ℝ)*X 2 1+(1493395343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_18 : ((2883027539/5000000000 : ℝ)*X 0 0+(5264731031/10000000000 : ℝ)*X 0 1+(-1493395343/10000000000 : ℝ)*X 0 2+(2883027539/5000000000 : ℝ)*X 1 0+(5264731031/10000000000 : ℝ)*X 1 1+(-1493395343/10000000000 : ℝ)*X 1 2+(2883027539/5000000000 : ℝ)*X 2 0+(5264731031/10000000000 : ℝ)*X 2 1+(-1493395343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((-1734353343/5000000000 : ℝ)*X 0 0+(3398623621/10000000000 : ℝ)*X 0 1+(-2979269809/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3362833113/10000000000 : ℝ)*X 1 0+(-3432916241/10000000000 : ℝ)*X 1 1+(-3009331087/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((5383816873/10000000000 : ℝ)*X 2 0+(5383816911/10000000000 : ℝ)*X 2 1+(1877602519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((1327288303/2500000000 : ℝ)*X 0 0+(5443249961/10000000000 : ℝ)*X 0 1+(-379665951/2000000000 : ℝ)*X 0 2+(1327288303/2500000000 : ℝ)*X 1 0+(5443249961/10000000000 : ℝ)*X 1 1+(-379665951/2000000000 : ℝ)*X 1 2+(1327288303/2500000000 : ℝ)*X 2 0+(5443249961/10000000000 : ℝ)*X 2 1+(-379665951/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306056_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((7789/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7789/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (78763728874403389319624031/5126977580000000000000000000000 : ℝ) := by norm_num
    linear_combination (290434939233/250000000000 : ℝ)*(base5) + (46452989/1000000000000 : ℝ)*(base39) + (158781973097/25000000000 : ℝ)*(base59) + (757814302071/250000000000 : ℝ)*(base60) + (13081448735811/1000000000000 : ℝ)*(major_s2_0) + (13081448735811/1000000000000 : ℝ)*(major_s2_1) + (13081448735811/1000000000000 : ℝ)*(major_s2_2) + (142913231/500000000000 : ℝ)*(sp_s2_1) + (3535738454089/200000000000 : ℝ)*(sp_s2_7) + (8838516460901/500000000000 : ℝ)*(sp_s2_8) + (18840432027377/1000000000000 : ℝ)*(sp_s2_9) + (1830282351737/250000000000 : ℝ)*(sp_s2_12) + (1373522181/1000000000000 : ℝ)*(sp_s2_20) + (66545821/50000000000 : ℝ)*(sp_s2_25) + (8484200080299/1000000000000 : ℝ)*(f.failure) + (3535738454089/200000000000 : ℝ)*(f.sum) + (5605953092029493981/51269775800000000000000000000000 : ℝ)*base62 + (89868534362927/142420000000000000000000000 : ℝ)*base65 + (3380499920967431/7199800000000000000000000000 : ℝ)*base66 + (308237441001143/712100000000000000000000000 : ℝ)*base69 + (891361003886677747/10253955160000000000000000000000 : ℝ)*base71 + (1745924601018711/7199800000000000000000000000 : ℝ)*base72 + (434882662084289/1439960000000000000000000000 : ℝ)*base75 + (438017648678909/1439960000000000000000000000 : ℝ)*base77 + (1200787746306769/3599900000000000000000000000 : ℝ)*base79 + (59193/50000000000000000 : ℝ)*base86 + (59193/50000000000000000 : ℝ)*base88 + (59193/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7789/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7789/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (177379363072491671591297307/12817443950000000000000000000000 : ℝ) := by norm_num
    linear_combination (1161338400817/1000000000000 : ℝ)*(base5) + (7825393/1000000000000 : ℝ)*(base39) + (3912697/500000000000 : ℝ)*(base40) + (1587649288509/250000000000 : ℝ)*(base59) + (3319638053907/1000000000000 : ℝ)*(base60) + (817560674557/62500000000 : ℝ)*(major_s2_0) + (817560674557/62500000000 : ℝ)*(major_s2_1) + (817560674557/62500000000 : ℝ)*(major_s2_2) + (21536591/125000000000 : ℝ)*(sp_s2_2) + (630392397/1000000000000 : ℝ)*(sp_s2_8) + (8839023435347/500000000000 : ℝ)*(sp_s2_13) + (2209677059787/125000000000 : ℝ)*(sp_s2_14) + (18839212978783/1000000000000 : ℝ)*(sp_s2_15) + (366127585067/50000000000 : ℝ)*(sp_s2_18) + (8483890102157/1000000000000 : ℝ)*(f.failure) + (8839023435347/500000000000 : ℝ)*(f.sum) + (91337089903731913/3204360987500000000000000000000 : ℝ)*base63 + (2153738536973/35605000000000000000000000 : ℝ)*base65 + (120662254778269/899975000000000000000000000 : ℝ)*base66 + (83264442377789/178025000000000000000000000 : ℝ)*base69 + (86917354852308769/2563488790000000000000000000000 : ℝ)*base70 + (1189991106253939/899975000000000000000000000 : ℝ)*base72 + (26888041679763/179995000000000000000000000 : ℝ)*base75 + (174840831128449/359990000000000000000000000 : ℝ)*base77 + (1122061369505511/1799950000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (10399/50000000000000000 : ℝ)*base86 + (10399/50000000000000000 : ℝ)*base88 + (10399/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-67/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-67/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23514356153952967937960277/3204360987500000000000000000000 : ℝ) := by norm_num
    linear_combination (297244659519/250000000000 : ℝ)*(base5) + (216240704341/1000000000000 : ℝ)*(base39) + (1185717/500000000000 : ℝ)*(base40) + (231132861973/1000000000000 : ℝ)*(base49) + (99113459573/100000000000 : ℝ)*(base59) + (229154825363/125000000000 : ℝ)*(major_s2_0) + (229154825363/125000000000 : ℝ)*(major_s2_1) + (229154825363/125000000000 : ℝ)*(major_s2_2) + (340601911/1000000000000 : ℝ)*(sp_s2_1) + (29649827/250000000000 : ℝ)*(sp_s2_9) + (71573813/1000000000000 : ℝ)*(sp_s2_15) + (49549922433/20000000000 : ℝ)*(sp_s2_19) + (2477155519739/1000000000000 : ℝ)*(sp_s2_20) + (733256917321/200000000000 : ℝ)*(sp_s2_21) + (297244659519/250000000000 : ℝ)*(f.failure) + (49549922433/20000000000 : ℝ)*(f.sum) + (76853412115504283/6408721975000000000000000000000 : ℝ)*base62 + (1049887400847/7121000000000000000000000 : ℝ)*base64 + (10941469150953/899975000000000000000000000 : ℝ)*base66 + (58040246423303/178025000000000000000000000 : ℝ)*base69 + (773390905901002753/2563488790000000000000000000000 : ℝ)*base70 + (51347798786953/56248437500000000000000000 : ℝ)*base72 + (108464579735829/359990000000000000000000000 : ℝ)*base75 + (46283587787199/89997500000000000000000000 : ℝ)*base77 + (194901185045991/899975000000000000000000000 : ℝ)*base78 + (1733/12500000000000000 : ℝ)*base86 + (1733/12500000000000000 : ℝ)*base88 + (1733/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((35999/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35999/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35999/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35999/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-7121/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-7121/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7789/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7789/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7789/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7789/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-67/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-67/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306056_s2 p hpa hpb X hX hprev1

#print axioms solution

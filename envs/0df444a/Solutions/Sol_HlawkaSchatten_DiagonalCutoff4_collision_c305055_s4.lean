-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305055_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:29:03.178878+00:00
-- url     : https://prove2.me/submissions/ceb5f5f4-defc-4b67-9a0e-912022e3262d

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
theorem collision_support_c305055_s4_s4_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-823500731/5000000000 : ℝ)*x 0 + (1482699679/2500000000 : ℝ)*x 1 + (2503624309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823500731/5000000000 : ℝ)^67 ≤ (9352999713723/100000000000000 : ℝ)^51 := by
    have hnat : (823500731 : ℕ)^67*100000000000000^51 ≤ 9352999713723^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823500731 5000000000 9352999713723 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1482699679/2500000000 : ℝ)^67 ≤ (12585573672481/25000000000000 : ℝ)^51 := by
    have hnat : (1482699679 : ℕ)^67*25000000000000^51 ≤ 12585573672481^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482699679 2500000000 12585573672481 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2503624309/5000000000 : ℝ)^67 ≤ (10076176396747/25000000000000 : ℝ)^51 := by
    have hnat : (2503624309 : ℕ)^67*25000000000000^51 ≤ 10076176396747^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503624309 5000000000 10076176396747 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-823500731/5000000000 : ℝ), (1482699679/2500000000 : ℝ), (2503624309/5000000000 : ℝ)] ![(9352999713723/100000000000000 : ℝ), (12585573672481/25000000000000 : ℝ), (10076176396747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-823500731/5000000000 : ℝ)|^67 ≤ (9352999713723/100000000000000 : ℝ)^51
        have hw : |(-823500731/5000000000 : ℝ)|=(823500731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1482699679/2500000000 : ℝ)|^67 ≤ (12585573672481/25000000000000 : ℝ)^51
        have hw : |(1482699679/2500000000 : ℝ)|=(1482699679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2503624309/5000000000 : ℝ)|^67 ≤ (10076176396747/25000000000000 : ℝ)^51
        have hw : |(2503624309/5000000000 : ℝ)|=(2503624309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4898888893/10000000000 : ℝ)*x 0 + (-11418431/200000000 : ℝ)*x 1 + (6650093939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4898888893/10000000000 : ℝ)^67 ≤ (39162761174107/100000000000000 : ℝ)^51 := by
    have hnat : (4898888893 : ℕ)^67*100000000000000^51 ≤ 39162761174107^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4898888893 10000000000 39162761174107 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11418431/200000000 : ℝ)^67 ≤ (2325320225617/100000000000000 : ℝ)^51 := by
    have hnat : (11418431 : ℕ)^67*100000000000000^51 ≤ 2325320225617^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11418431 200000000 2325320225617 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6650093939/10000000000 : ℝ)^67 ≤ (11702383715817/20000000000000 : ℝ)^51 := by
    have hnat : (6650093939 : ℕ)^67*20000000000000^51 ≤ 11702383715817^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6650093939 10000000000 11702383715817 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4898888893/10000000000 : ℝ), (-11418431/200000000 : ℝ), (6650093939/10000000000 : ℝ)] ![(39162761174107/100000000000000 : ℝ), (2325320225617/100000000000000 : ℝ), (11702383715817/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4898888893/10000000000 : ℝ)|^67 ≤ (39162761174107/100000000000000 : ℝ)^51
        have hw : |(4898888893/10000000000 : ℝ)|=(4898888893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11418431/200000000 : ℝ)|^67 ≤ (2325320225617/100000000000000 : ℝ)^51
        have hw : |(-11418431/200000000 : ℝ)|=(11418431/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6650093939/10000000000 : ℝ)|^67 ≤ (11702383715817/20000000000000 : ℝ)^51
        have hw : |(6650093939/10000000000 : ℝ)|=(6650093939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4871437957/10000000000 : ℝ)*x 0 + (6072623961/10000000000 : ℝ)*x 1 + (-65034177/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4871437957/10000000000 : ℝ)^67 ≤ (19437359824077/50000000000000 : ℝ)^51 := by
    have hnat : (4871437957 : ℕ)^67*50000000000000^51 ≤ 19437359824077^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871437957 10000000000 19437359824077 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6072623961/10000000000 : ℝ)^67 ≤ (51929727095137/100000000000000 : ℝ)^51 := by
    have hnat : (6072623961 : ℕ)^67*100000000000000^51 ≤ 51929727095137^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6072623961 10000000000 51929727095137 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65034177/400000000 : ℝ)^67 ≤ (9195553247871/100000000000000 : ℝ)^51 := by
    have hnat : (65034177 : ℕ)^67*100000000000000^51 ≤ 9195553247871^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65034177 400000000 9195553247871 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4871437957/10000000000 : ℝ), (6072623961/10000000000 : ℝ), (-65034177/400000000 : ℝ)] ![(19437359824077/50000000000000 : ℝ), (51929727095137/100000000000000 : ℝ), (9195553247871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4871437957/10000000000 : ℝ)|^67 ≤ (19437359824077/50000000000000 : ℝ)^51
        have hw : |(4871437957/10000000000 : ℝ)|=(4871437957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6072623961/10000000000 : ℝ)|^67 ≤ (51929727095137/100000000000000 : ℝ)^51
        have hw : |(6072623961/10000000000 : ℝ)|=(6072623961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65034177/400000000 : ℝ)|^67 ≤ (9195553247871/100000000000000 : ℝ)^51
        have hw : |(-65034177/400000000 : ℝ)|=(65034177/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (318622969/500000000 : ℝ)*x 0 + (244921159/625000000 : ℝ)*x 1 + (75482667/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (318622969/500000000 : ℝ)^67 ≤ (55323954727407/100000000000000 : ℝ)^51 := by
    have hnat : (318622969 : ℕ)^67*100000000000000^51 ≤ 55323954727407^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318622969 500000000 55323954727407 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244921159/625000000 : ℝ)^67 ≤ (5841654994649/20000000000000 : ℝ)^51 := by
    have hnat : (244921159 : ℕ)^67*20000000000000^51 ≤ 5841654994649^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244921159 625000000 5841654994649 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75482667/312500000 : ℝ)^67 ≤ (15467770283743/100000000000000 : ℝ)^51 := by
    have hnat : (75482667 : ℕ)^67*100000000000000^51 ≤ 15467770283743^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75482667 312500000 15467770283743 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(318622969/500000000 : ℝ), (244921159/625000000 : ℝ), (75482667/312500000 : ℝ)] ![(55323954727407/100000000000000 : ℝ), (5841654994649/20000000000000 : ℝ), (15467770283743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(318622969/500000000 : ℝ)|^67 ≤ (55323954727407/100000000000000 : ℝ)^51
        have hw : |(318622969/500000000 : ℝ)|=(318622969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(244921159/625000000 : ℝ)|^67 ≤ (5841654994649/20000000000000 : ℝ)^51
        have hw : |(244921159/625000000 : ℝ)|=(244921159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75482667/312500000 : ℝ)|^67 ≤ (15467770283743/100000000000000 : ℝ)^51
        have hw : |(75482667/312500000 : ℝ)|=(75482667/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-826390073/5000000000 : ℝ)*x 0 + (531411751/1250000000 : ℝ)*x 1 + (6614144067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826390073/5000000000 : ℝ)^67 ≤ (4698067330657/50000000000000 : ℝ)^51 := by
    have hnat : (826390073 : ℕ)^67*50000000000000^51 ≤ 4698067330657^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826390073 5000000000 4698067330657 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531411751/1250000000 : ℝ)^67 ≤ (32507139381011/100000000000000 : ℝ)^51 := by
    have hnat : (531411751 : ℕ)^67*100000000000000^51 ≤ 32507139381011^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531411751 1250000000 32507139381011 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6614144067/10000000000 : ℝ)^67 ≤ (58096725941111/100000000000000 : ℝ)^51 := by
    have hnat : (6614144067 : ℕ)^67*100000000000000^51 ≤ 58096725941111^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6614144067 10000000000 58096725941111 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-826390073/5000000000 : ℝ), (531411751/1250000000 : ℝ), (6614144067/10000000000 : ℝ)] ![(4698067330657/50000000000000 : ℝ), (32507139381011/100000000000000 : ℝ), (58096725941111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-826390073/5000000000 : ℝ)|^67 ≤ (4698067330657/50000000000000 : ℝ)^51
        have hw : |(-826390073/5000000000 : ℝ)|=(826390073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531411751/1250000000 : ℝ)|^67 ≤ (32507139381011/100000000000000 : ℝ)^51
        have hw : |(531411751/1250000000 : ℝ)|=(531411751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6614144067/10000000000 : ℝ)|^67 ≤ (58096725941111/100000000000000 : ℝ)^51
        have hw : |(6614144067/10000000000 : ℝ)|=(6614144067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3656169679/10000000000 : ℝ)*x 0 + (156993/2000000000 : ℝ)*x 1 + (493577491/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3656169679/10000000000 : ℝ)^67 ≤ (26664691770407/100000000000000 : ℝ)^51 := by
    have hnat : (3656169679 : ℕ)^67*100000000000000^51 ≤ 26664691770407^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3656169679 10000000000 26664691770407 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156993/2000000000 : ℝ)^67 ≤ (404538807/100000000000000 : ℝ)^51 := by
    have hnat : (156993 : ℕ)^67*100000000000000^51 ≤ 404538807^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156993 2000000000 404538807 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493577491/625000000 : ℝ)^67 ≤ (73334903677191/100000000000000 : ℝ)^51 := by
    have hnat : (493577491 : ℕ)^67*100000000000000^51 ≤ 73334903677191^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493577491 625000000 73334903677191 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3656169679/10000000000 : ℝ), (156993/2000000000 : ℝ), (493577491/625000000 : ℝ)] ![(26664691770407/100000000000000 : ℝ), (404538807/100000000000000 : ℝ), (73334903677191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3656169679/10000000000 : ℝ)|^67 ≤ (26664691770407/100000000000000 : ℝ)^51
        have hw : |(3656169679/10000000000 : ℝ)|=(3656169679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156993/2000000000 : ℝ)|^67 ≤ (404538807/100000000000000 : ℝ)^51
        have hw : |(156993/2000000000 : ℝ)|=(156993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(493577491/625000000 : ℝ)|^67 ≤ (73334903677191/100000000000000 : ℝ)^51
        have hw : |(493577491/625000000 : ℝ)|=(493577491/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1812473377/5000000000 : ℝ)*x 0 + (7557326443/10000000000 : ℝ)*x 1 + (-93052087/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1812473377/5000000000 : ℝ)^67 ≤ (26365943681777/100000000000000 : ℝ)^51 := by
    have hnat : (1812473377 : ℕ)^67*100000000000000^51 ≤ 26365943681777^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812473377 5000000000 26365943681777 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7557326443/10000000000 : ℝ)^67 ≤ (13843285515021/20000000000000 : ℝ)^51 := by
    have hnat : (7557326443 : ℕ)^67*20000000000000^51 ≤ 13843285515021^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7557326443 10000000000 13843285515021 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93052087/1000000000 : ℝ)^67 ≤ (2208814365973/50000000000000 : ℝ)^51 := by
    have hnat : (93052087 : ℕ)^67*50000000000000^51 ≤ 2208814365973^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93052087 1000000000 2208814365973 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1812473377/5000000000 : ℝ), (7557326443/10000000000 : ℝ), (-93052087/1000000000 : ℝ)] ![(26365943681777/100000000000000 : ℝ), (13843285515021/20000000000000 : ℝ), (2208814365973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1812473377/5000000000 : ℝ)|^67 ≤ (26365943681777/100000000000000 : ℝ)^51
        have hw : |(1812473377/5000000000 : ℝ)|=(1812473377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7557326443/10000000000 : ℝ)|^67 ≤ (13843285515021/20000000000000 : ℝ)^51
        have hw : |(7557326443/10000000000 : ℝ)|=(7557326443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93052087/1000000000 : ℝ)|^67 ≤ (2208814365973/50000000000000 : ℝ)^51
        have hw : |(-93052087/1000000000 : ℝ)|=(93052087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4545360871/10000000000 : ℝ)*x 0 + (6534401379/10000000000 : ℝ)*x 1 + (136798089/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4545360871/10000000000 : ℝ)^67 ≤ (443658545109/1250000000000 : ℝ)^51 := by
    have hnat : (4545360871 : ℕ)^67*1250000000000^51 ≤ 443658545109^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545360871 10000000000 443658545109 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6534401379/10000000000 : ℝ)^67 ≤ (14294572373543/25000000000000 : ℝ)^51 := by
    have hnat : (6534401379 : ℕ)^67*25000000000000^51 ≤ 14294572373543^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6534401379 10000000000 14294572373543 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136798089/1000000000 : ℝ)^67 ≤ (1465805376437/20000000000000 : ℝ)^51 := by
    have hnat : (136798089 : ℕ)^67*20000000000000^51 ≤ 1465805376437^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136798089 1000000000 1465805376437 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4545360871/10000000000 : ℝ), (6534401379/10000000000 : ℝ), (136798089/1000000000 : ℝ)] ![(443658545109/1250000000000 : ℝ), (14294572373543/25000000000000 : ℝ), (1465805376437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4545360871/10000000000 : ℝ)|^67 ≤ (443658545109/1250000000000 : ℝ)^51
        have hw : |(4545360871/10000000000 : ℝ)|=(4545360871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6534401379/10000000000 : ℝ)|^67 ≤ (14294572373543/25000000000000 : ℝ)^51
        have hw : |(6534401379/10000000000 : ℝ)|=(6534401379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136798089/1000000000 : ℝ)|^67 ≤ (1465805376437/20000000000000 : ℝ)^51
        have hw : |(136798089/1000000000 : ℝ)|=(136798089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-285457071/5000000000 : ℝ)*x 0 + (4629416699/10000000000 : ℝ)*x 1 + (3445714883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (285457071/5000000000 : ℝ)^67 ≤ (2325280587679/100000000000000 : ℝ)^51 := by
    have hnat : (285457071 : ℕ)^67*100000000000000^51 ≤ 2325280587679^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285457071 5000000000 2325280587679 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4629416699/10000000000 : ℝ)^67 ≤ (36357443692443/100000000000000 : ℝ)^51 := by
    have hnat : (4629416699 : ℕ)^67*100000000000000^51 ≤ 36357443692443^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4629416699 10000000000 36357443692443 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3445714883/5000000000 : ℝ)^67 ≤ (61317275696913/100000000000000 : ℝ)^51 := by
    have hnat : (3445714883 : ℕ)^67*100000000000000^51 ≤ 61317275696913^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3445714883 5000000000 61317275696913 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-285457071/5000000000 : ℝ), (4629416699/10000000000 : ℝ), (3445714883/5000000000 : ℝ)] ![(2325280587679/100000000000000 : ℝ), (36357443692443/100000000000000 : ℝ), (61317275696913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-285457071/5000000000 : ℝ)|^67 ≤ (2325280587679/100000000000000 : ℝ)^51
        have hw : |(-285457071/5000000000 : ℝ)|=(285457071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4629416699/10000000000 : ℝ)|^67 ≤ (36357443692443/100000000000000 : ℝ)^51
        have hw : |(4629416699/10000000000 : ℝ)|=(4629416699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3445714883/5000000000 : ℝ)|^67 ≤ (61317275696913/100000000000000 : ℝ)^51
        have hw : |(3445714883/5000000000 : ℝ)|=(3445714883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3216325787/10000000000 : ℝ)*x 0 + (-282561383/10000000000 : ℝ)*x 1 + (1019874781/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3216325787/10000000000 : ℝ)^67 ≤ (11266170560969/50000000000000 : ℝ)^51 := by
    have hnat : (3216325787 : ℕ)^67*50000000000000^51 ≤ 11266170560969^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3216325787 10000000000 11266170560969 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282561383/10000000000 : ℝ)^67 ≤ (922969636177/100000000000000 : ℝ)^51 := by
    have hnat : (282561383 : ℕ)^67*100000000000000^51 ≤ 922969636177^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282561383 10000000000 922969636177 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019874781/1250000000 : ℝ)^67 ≤ (1913617230671/2500000000000 : ℝ)^51 := by
    have hnat : (1019874781 : ℕ)^67*2500000000000^51 ≤ 1913617230671^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019874781 1250000000 1913617230671 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3216325787/10000000000 : ℝ), (-282561383/10000000000 : ℝ), (1019874781/1250000000 : ℝ)] ![(11266170560969/50000000000000 : ℝ), (922969636177/100000000000000 : ℝ), (1913617230671/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3216325787/10000000000 : ℝ)|^67 ≤ (11266170560969/50000000000000 : ℝ)^51
        have hw : |(3216325787/10000000000 : ℝ)|=(3216325787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282561383/10000000000 : ℝ)|^67 ≤ (922969636177/100000000000000 : ℝ)^51
        have hw : |(-282561383/10000000000 : ℝ)|=(282561383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019874781/1250000000 : ℝ)|^67 ≤ (1913617230671/2500000000000 : ℝ)^51
        have hw : |(1019874781/1250000000 : ℝ)|=(1019874781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (54029181/80000000 : ℝ)*x 0 + (1197197117/2500000000 : ℝ)*x 1 + (-561985981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54029181/80000000 : ℝ)^67 ≤ (29855905802703/50000000000000 : ℝ)^51 := by
    have hnat : (54029181 : ℕ)^67*50000000000000^51 ≤ 29855905802703^51*80000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54029181 80000000 29855905802703 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1197197117/2500000000 : ℝ)^67 ≤ (19005280967287/50000000000000 : ℝ)^51 := by
    have hnat : (1197197117 : ℕ)^67*50000000000000^51 ≤ 19005280967287^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197197117 2500000000 19005280967287 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561985981/10000000000 : ℝ)^67 ≤ (2277626441513/100000000000000 : ℝ)^51 := by
    have hnat : (561985981 : ℕ)^67*100000000000000^51 ≤ 2277626441513^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561985981 10000000000 2277626441513 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54029181/80000000 : ℝ), (1197197117/2500000000 : ℝ), (-561985981/10000000000 : ℝ)] ![(29855905802703/50000000000000 : ℝ), (19005280967287/50000000000000 : ℝ), (2277626441513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54029181/80000000 : ℝ)|^67 ≤ (29855905802703/50000000000000 : ℝ)^51
        have hw : |(54029181/80000000 : ℝ)|=(54029181/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1197197117/2500000000 : ℝ)|^67 ≤ (19005280967287/50000000000000 : ℝ)^51
        have hw : |(1197197117/2500000000 : ℝ)|=(1197197117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-561985981/10000000000 : ℝ)|^67 ≤ (2277626441513/100000000000000 : ℝ)^51
        have hw : |(-561985981/10000000000 : ℝ)|=(561985981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4193208473/5000000000 : ℝ)*x 0 + (508490621/2000000000 : ℝ)*x 1 + (219592499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193208473/5000000000 : ℝ)^67 ≤ (79359776265851/100000000000000 : ℝ)^51 := by
    have hnat : (4193208473 : ℕ)^67*100000000000000^51 ≤ 79359776265851^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193208473 5000000000 79359776265851 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508490621/2000000000 : ℝ)^67 ≤ (3308991392367/20000000000000 : ℝ)^51 := by
    have hnat : (508490621 : ℕ)^67*20000000000000^51 ≤ 3308991392367^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508490621 2000000000 3308991392367 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219592499/2500000000 : ℝ)^67 ≤ (4095266755823/100000000000000 : ℝ)^51 := by
    have hnat : (219592499 : ℕ)^67*100000000000000^51 ≤ 4095266755823^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219592499 2500000000 4095266755823 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193208473/5000000000 : ℝ), (508490621/2000000000 : ℝ), (219592499/2500000000 : ℝ)] ![(79359776265851/100000000000000 : ℝ), (3308991392367/20000000000000 : ℝ), (4095266755823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193208473/5000000000 : ℝ)|^67 ≤ (79359776265851/100000000000000 : ℝ)^51
        have hw : |(4193208473/5000000000 : ℝ)|=(4193208473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508490621/2000000000 : ℝ)|^67 ≤ (3308991392367/20000000000000 : ℝ)^51
        have hw : |(508490621/2000000000 : ℝ)|=(508490621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219592499/2500000000 : ℝ)|^67 ≤ (4095266755823/100000000000000 : ℝ)^51
        have hw : |(219592499/2500000000 : ℝ)|=(219592499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-55385481/625000000 : ℝ)*x 0 + (7429305377/10000000000 : ℝ)*x 1 + (1906470957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55385481/625000000 : ℝ)^67 ≤ (4143094399407/100000000000000 : ℝ)^51 := by
    have hnat : (55385481 : ℕ)^67*100000000000000^51 ≤ 4143094399407^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55385481 625000000 4143094399407 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7429305377/10000000000 : ℝ)^67 ≤ (8460019948389/12500000000000 : ℝ)^51 := by
    have hnat : (7429305377 : ℕ)^67*12500000000000^51 ≤ 8460019948389^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7429305377 10000000000 8460019948389 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1906470957/5000000000 : ℝ)^67 ≤ (7044186498591/25000000000000 : ℝ)^51 := by
    have hnat : (1906470957 : ℕ)^67*25000000000000^51 ≤ 7044186498591^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906470957 5000000000 7044186498591 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55385481/625000000 : ℝ), (7429305377/10000000000 : ℝ), (1906470957/5000000000 : ℝ)] ![(4143094399407/100000000000000 : ℝ), (8460019948389/12500000000000 : ℝ), (7044186498591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55385481/625000000 : ℝ)|^67 ≤ (4143094399407/100000000000000 : ℝ)^51
        have hw : |(-55385481/625000000 : ℝ)|=(55385481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7429305377/10000000000 : ℝ)|^67 ≤ (8460019948389/12500000000000 : ℝ)^51
        have hw : |(7429305377/10000000000 : ℝ)|=(7429305377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1906470957/5000000000 : ℝ)|^67 ≤ (7044186498591/25000000000000 : ℝ)^51
        have hw : |(1906470957/5000000000 : ℝ)|=(1906470957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3408368343/5000000000 : ℝ)*x 0 + (-15424061/10000000000 : ℝ)*x 1 + (1233551611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3408368343/5000000000 : ℝ)^67 ≤ (2417826991971/4000000000000 : ℝ)^51 := by
    have hnat : (3408368343 : ℕ)^67*4000000000000^51 ≤ 2417826991971^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3408368343 5000000000 2417826991971 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15424061/10000000000 : ℝ)^67 ≤ (10116609999/50000000000000 : ℝ)^51 := by
    have hnat : (15424061 : ℕ)^67*50000000000000^51 ≤ 10116609999^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15424061 10000000000 10116609999 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1233551611/2500000000 : ℝ)^67 ≤ (39534091970183/100000000000000 : ℝ)^51 := by
    have hnat : (1233551611 : ℕ)^67*100000000000000^51 ≤ 39534091970183^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233551611 2500000000 39534091970183 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3408368343/5000000000 : ℝ), (-15424061/10000000000 : ℝ), (1233551611/2500000000 : ℝ)] ![(2417826991971/4000000000000 : ℝ), (10116609999/50000000000000 : ℝ), (39534091970183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3408368343/5000000000 : ℝ)|^67 ≤ (2417826991971/4000000000000 : ℝ)^51
        have hw : |(3408368343/5000000000 : ℝ)|=(3408368343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15424061/10000000000 : ℝ)|^67 ≤ (10116609999/50000000000000 : ℝ)^51
        have hw : |(-15424061/10000000000 : ℝ)|=(15424061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1233551611/2500000000 : ℝ)|^67 ≤ (39534091970183/100000000000000 : ℝ)^51
        have hw : |(1233551611/2500000000 : ℝ)|=(1233551611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (179976543/625000000 : ℝ)*x 0 + (7802395631/10000000000 : ℝ)*x 1 + (-37714709/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179976543/625000000 : ℝ)^67 ≤ (19485689360451/100000000000000 : ℝ)^51 := by
    have hnat : (179976543 : ℕ)^67*100000000000000^51 ≤ 19485689360451^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179976543 625000000 19485689360451 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7802395631/10000000000 : ℝ)^67 ≤ (36090021334899/50000000000000 : ℝ)^51 := by
    have hnat : (7802395631 : ℕ)^67*50000000000000^51 ≤ 36090021334899^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7802395631 10000000000 36090021334899 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37714709/250000000 : ℝ)^67 ≤ (833426795041/10000000000000 : ℝ)^51 := by
    have hnat : (37714709 : ℕ)^67*10000000000000^51 ≤ 833426795041^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37714709 250000000 833426795041 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(179976543/625000000 : ℝ), (7802395631/10000000000 : ℝ), (-37714709/250000000 : ℝ)] ![(19485689360451/100000000000000 : ℝ), (36090021334899/50000000000000 : ℝ), (833426795041/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(179976543/625000000 : ℝ)|^67 ≤ (19485689360451/100000000000000 : ℝ)^51
        have hw : |(179976543/625000000 : ℝ)|=(179976543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7802395631/10000000000 : ℝ)|^67 ≤ (36090021334899/50000000000000 : ℝ)^51
        have hw : |(7802395631/10000000000 : ℝ)|=(7802395631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37714709/250000000 : ℝ)|^67 ≤ (833426795041/10000000000000 : ℝ)^51
        have hw : |(-37714709/250000000 : ℝ)|=(37714709/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305055_s4_s4_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8157063891/10000000000 : ℝ)*x 0 + (2201432289/10000000000 : ℝ)*x 1 + (1704760553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8157063891/10000000000 : ℝ)^67 ≤ (765208493873/1000000000000 : ℝ)^51 := by
    have hnat : (8157063891 : ℕ)^67*1000000000000^51 ≤ 765208493873^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8157063891 10000000000 765208493873 1000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201432289/10000000000 : ℝ)^67 ≤ (3423223452857/25000000000000 : ℝ)^51 := by
    have hnat : (2201432289 : ℕ)^67*25000000000000^51 ≤ 3423223452857^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201432289 10000000000 3423223452857 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704760553/10000000000 : ℝ)^67 ≤ (4893128392357/50000000000000 : ℝ)^51 := by
    have hnat : (1704760553 : ℕ)^67*50000000000000^51 ≤ 4893128392357^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704760553 10000000000 4893128392357 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8157063891/10000000000 : ℝ), (2201432289/10000000000 : ℝ), (1704760553/10000000000 : ℝ)] ![(765208493873/1000000000000 : ℝ), (3423223452857/25000000000000 : ℝ), (4893128392357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8157063891/10000000000 : ℝ)|^67 ≤ (765208493873/1000000000000 : ℝ)^51
        have hw : |(8157063891/10000000000 : ℝ)|=(8157063891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2201432289/10000000000 : ℝ)|^67 ≤ (3423223452857/25000000000000 : ℝ)^51
        have hw : |(2201432289/10000000000 : ℝ)|=(2201432289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1704760553/10000000000 : ℝ)|^67 ≤ (4893128392357/50000000000000 : ℝ)^51
        have hw : |(1704760553/10000000000 : ℝ)|=(1704760553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305055_s4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((39131/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39131/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76439/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76439/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38789/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38789/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((67941/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67941/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4193/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4193/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13779/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13779/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (39131/50000 : ℝ) ^ (133/32 : ℝ) ≤ (36105312099251000263/100000000000000000000 : ℝ) := by
    have hpowers : (39131/50000 : ℝ)^133 ≤ (36105312099251000263/100000000000000000000 : ℝ)^32 := by
      have hnat : (39131 : ℕ)^133*100000000000000000000^32 ≤ 36105312099251000263^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39131 50000 36105312099251000263 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39131/50000 : ℝ)) (X := (36105312099251000263/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (136105312099251000263/100000000000000000000 : ℝ) ≤ (10769872069614611/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (136105312099251000263/100000000000000000000 : ℝ)^32 ≤ (10769872069614611/10000000000000000 : ℝ)^133 := by
      have hnat : (136105312099251000263 : ℕ)^32*10000000000000000^133 ≤ 10769872069614611^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        136105312099251000263 100000000000000000000 10769872069614611 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10769872069614611/10000000000000000 : ℝ)) (X := (136105312099251000263/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (86105312099251000263/50000000000000000000 : ℝ) ≤ (11397152955336223/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (86105312099251000263/50000000000000000000 : ℝ)^32 ≤ (11397152955336223/10000000000000000 : ℝ)^133 := by
      have hnat : (86105312099251000263 : ℕ)^32*10000000000000000^133 ≤ 11397152955336223^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86105312099251000263 50000000000000000000 11397152955336223 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11397152955336223/10000000000000000 : ℝ)) (X := (86105312099251000263/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(769872069614611/7826200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(156820221430403/1956550000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (39131/50000 : ℝ)) (alpha := (769872069614611/7826200000000000 : ℝ)) (beta := (156820221430403/1956550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (39131/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(769872069614611/7826200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(156820221430403/1956550000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (76439/100000 : ℝ) ^ (133/32 : ℝ) ≤ (3273617665309099321/10000000000000000000 : ℝ) := by
    have hpowers : (76439/100000 : ℝ)^133 ≤ (3273617665309099321/10000000000000000000 : ℝ)^32 := by
      have hnat : (76439 : ℕ)^133*10000000000000000000^32 ≤ 3273617665309099321^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76439 100000 3273617665309099321 10000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76439/100000 : ℝ)) (X := (3273617665309099321/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (13273617665309099321/10000000000000000000 : ℝ) ≤ (10705116834355611/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (13273617665309099321/10000000000000000000 : ℝ)^32 ≤ (10705116834355611/10000000000000000 : ℝ)^133 := by
      have hnat : (13273617665309099321 : ℕ)^32*10000000000000000^133 ≤ 10705116834355611^133*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13273617665309099321 10000000000000000000 10705116834355611 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10705116834355611/10000000000000000 : ℝ)) (X := (13273617665309099321/10000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (8273617665309099321/5000000000000000000 : ℝ) ≤ (5644112672537557/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (8273617665309099321/5000000000000000000 : ℝ)^32 ≤ (5644112672537557/5000000000000000 : ℝ)^133 := by
      have hnat : (8273617665309099321 : ℕ)^32*5000000000000000^133 ≤ 5644112672537557^133*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8273617665309099321 5000000000000000000 5644112672537557 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5644112672537557/5000000000000000 : ℝ)) (X := (8273617665309099321/5000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(705116834355611/7643900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(583108510719503/7643900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (76439/100000 : ℝ)) (alpha := (705116834355611/7643900000000000 : ℝ)) (beta := (583108510719503/7643900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (76439/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(705116834355611/7643900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(583108510719503/7643900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (38789/50000 : ℝ) ^ (133/32 : ℝ) ≤ (435146988529876263/1250000000000000000 : ℝ) := by
    have hpowers : (38789/50000 : ℝ)^133 ≤ (435146988529876263/1250000000000000000 : ℝ)^32 := by
      have hnat : (38789 : ℕ)^133*1250000000000000000^32 ≤ 435146988529876263^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38789 50000 435146988529876263 1250000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38789/50000 : ℝ)) (X := (435146988529876263/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (1685146988529876263/1250000000000000000 : ℝ) ≤ (5372577664174893/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (1685146988529876263/1250000000000000000 : ℝ)^32 ≤ (5372577664174893/5000000000000000 : ℝ)^133 := by
      have hnat : (1685146988529876263 : ℕ)^32*5000000000000000^133 ≤ 5372577664174893^133*1250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1685146988529876263 1250000000000000000 5372577664174893 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5372577664174893/5000000000000000 : ℝ)) (X := (1685146988529876263/1250000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (1060146988529876263/625000000000000000 : ℝ) ≤ (11355720450377579/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (1060146988529876263/625000000000000000 : ℝ)^32 ≤ (11355720450377579/10000000000000000 : ℝ)^133 := by
      have hnat : (1060146988529876263 : ℕ)^32*10000000000000000^133 ≤ 11355720450377579^133*625000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1060146988529876263 625000000000000000 11355720450377579 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11355720450377579/10000000000000000 : ℝ)) (X := (1060146988529876263/625000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(372577664174893/3878900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(610565122027793/7757800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (38789/50000 : ℝ)) (alpha := (372577664174893/3878900000000000 : ℝ)) (beta := (610565122027793/7757800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (38789/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(372577664174893/3878900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(610565122027793/7757800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-823500731/5000000000 : ℝ)*X 0 0+(1482699679/2500000000 : ℝ)*X 0 1+(2503624309/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((4898888893/10000000000 : ℝ)*X 1 0+(-11418431/200000000 : ℝ)*X 1 1+(6650093939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((4871437957/10000000000 : ℝ)*X 2 0+(6072623961/10000000000 : ℝ)*X 2 1+(-65034177/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((318622969/500000000 : ℝ)*X 0 0+(244921159/625000000 : ℝ)*X 0 1+(75482667/312500000 : ℝ)*X 0 2+(318622969/500000000 : ℝ)*X 1 0+(244921159/625000000 : ℝ)*X 1 1+(75482667/312500000 : ℝ)*X 1 2+(318622969/500000000 : ℝ)*X 2 0+(244921159/625000000 : ℝ)*X 2 1+(75482667/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-826390073/5000000000 : ℝ)*X 0 0+(531411751/1250000000 : ℝ)*X 0 1+(6614144067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((3656169679/10000000000 : ℝ)*X 1 0+(156993/2000000000 : ℝ)*X 1 1+(493577491/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((1812473377/5000000000 : ℝ)*X 2 0+(7557326443/10000000000 : ℝ)*X 2 1+(-93052087/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((4545360871/10000000000 : ℝ)*X 0 0+(6534401379/10000000000 : ℝ)*X 0 1+(136798089/1000000000 : ℝ)*X 0 2+(4545360871/10000000000 : ℝ)*X 1 0+(6534401379/10000000000 : ℝ)*X 1 1+(136798089/1000000000 : ℝ)*X 1 2+(4545360871/10000000000 : ℝ)*X 2 0+(6534401379/10000000000 : ℝ)*X 2 1+(136798089/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-285457071/5000000000 : ℝ)*X 0 0+(4629416699/10000000000 : ℝ)*X 0 1+(3445714883/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((3216325787/10000000000 : ℝ)*X 1 0+(-282561383/10000000000 : ℝ)*X 1 1+(1019874781/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((54029181/80000000 : ℝ)*X 2 0+(1197197117/2500000000 : ℝ)*X 2 1+(-561985981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((4193208473/5000000000 : ℝ)*X 0 0+(508490621/2000000000 : ℝ)*X 0 1+(219592499/2500000000 : ℝ)*X 0 2+(4193208473/5000000000 : ℝ)*X 1 0+(508490621/2000000000 : ℝ)*X 1 1+(219592499/2500000000 : ℝ)*X 1 2+(4193208473/5000000000 : ℝ)*X 2 0+(508490621/2000000000 : ℝ)*X 2 1+(219592499/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-55385481/625000000 : ℝ)*X 0 0+(7429305377/10000000000 : ℝ)*X 0 1+(1906470957/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((3408368343/5000000000 : ℝ)*X 1 0+(-15424061/10000000000 : ℝ)*X 1 1+(1233551611/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((179976543/625000000 : ℝ)*X 2 0+(7802395631/10000000000 : ℝ)*X 2 1+(-37714709/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((8157063891/10000000000 : ℝ)*X 0 0+(2201432289/10000000000 : ℝ)*X 0 1+(1704760553/10000000000 : ℝ)*X 0 2+(8157063891/10000000000 : ℝ)*X 1 0+(2201432289/10000000000 : ℝ)*X 1 1+(1704760553/10000000000 : ℝ)*X 1 2+(8157063891/10000000000 : ℝ)*X 2 0+(2201432289/10000000000 : ℝ)*X 2 1+(1704760553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305055_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((67941/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67941/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (54686177237110024722003751623993/2900577911740025000000000000000000000 : ℝ) := by norm_num
    linear_combination (531251528861/1000000000000 : ℝ)*(base7) + (2748087/1000000000000 : ℝ)*(base49) + (345709/200000000000 : ℝ)*(base60) + (2608227084733/1000000000000 : ℝ)*(major_s4_0) + (2608227084733/1000000000000 : ℝ)*(major_s4_1) + (2608227084733/1000000000000 : ℝ)*(major_s4_2) + (26756329/1000000000000 : ℝ)*(sp_s4_0) + (1107269/250000000000 : ℝ)*(sp_s4_6) + (3179872927283/1000000000000 : ℝ)*(sp_s4_7) + (3179962622147/1000000000000 : ℝ)*(sp_s4_8) + (3179939487623/1000000000000 : ℝ)*(sp_s4_9) + (139798330321/62500000000 : ℝ)*(sp_s4_13) + (12587707/200000000000 : ℝ)*(sp_s4_14) + (5783631/250000000000 : ℝ)*(sp_s4_23) + (1705526185351/1000000000000 : ℝ)*(f.failure) + (3179962622147/1000000000000 : ℝ)*(f.sum) + (53329089681136684599/148249618550000000000000000000000 : ℝ)*base63 + (4075846340981911/7757800000000000000000000000 : ℝ)*base64 + (1855154337906271/7643900000000000000000000000 : ℝ)*base67 + (1322244326382959/3878900000000000000000000000 : ℝ)*base69 + (72322271351612886297/151785235900000000000000000000000 : ℝ)*base70 + (87872987213081/1956550000000000000000000000 : ℝ)*base72 + (10535282003237/7643900000000000000000000000 : ℝ)*base74 + (1642457263851157/7826200000000000000000000000 : ℝ)*base76 + (82168386139528896693/299113450900000000000000000000000 : ℝ)*base79 + (451/781250000000000 : ℝ)*base87 + (451/781250000000000 : ℝ)*base89 + (451/781250000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4193/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4193/6250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (406225436276974182722368799943/46409246587840400000000000000000000 : ℝ) := by norm_num
    linear_combination (81626371769/200000000000 : ℝ)*(base7) + (80321/250000000000 : ℝ)*(base40) + (454178634209/200000000000 : ℝ)*(major_s4_0) + (454178634209/200000000000 : ℝ)*(major_s4_1) + (454178634209/200000000000 : ℝ)*(major_s4_2) + (5005003/250000000000 : ℝ)*(sp_s4_0) + (1527577/100000000000 : ℝ)*(sp_s4_2) + (124446977/1000000000000 : ℝ)*(sp_s4_8) + (1401279638599/500000000000 : ℝ)*(sp_s4_14) + (700614573193/250000000000 : ℝ)*(sp_s4_15) + (1401283731989/500000000000 : ℝ)*(sp_s4_16) + (473260718471/250000000000 : ℝ)*(sp_s4_20) + (1721269/500000000000 : ℝ)*(sp_s4_21) + (3168417/100000000000 : ℝ)*(sp_s4_27) + (185617837401/125000000000 : ℝ)*(f.failure) + (700645684937/250000000000 : ℝ)*(f.sum) + (10862066395699455669/29649923710000000000000000000000 : ℝ)*base62 + (76802514159383/1551560000000000000000000000 : ℝ)*base64 + (150151175198747/1528780000000000000000000000 : ℝ)*base66 + (541226431485981/775780000000000000000000000 : ℝ)*base68 + (12024446850653645693/30357047180000000000000000000000 : ℝ)*base70 + (7794005699699/15652400000000000000000000 : ℝ)*base72 + (502839721484673/1528780000000000000000000000 : ℝ)*base74 + (612446193063277/1565240000000000000000000000 : ℝ)*base76 + (13575835973477465161/59822690180000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (593/3125000000000000 : ℝ)*base86 + (593/3125000000000000 : ℝ)*base88 + (593/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13779/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13779/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23869212431687849756045171250831/2900577911740025000000000000000000000 : ℝ) := by norm_num
    linear_combination (292386973051/500000000000 : ℝ)*(base7) + (52804754581/1000000000000 : ℝ)*(base40) + (966131/1000000000000 : ℝ)*(base43) + (13221/62500000000 : ℝ)*(base59) + (2173142677481/1000000000000 : ℝ)*(major_s4_0) + (43462834227/20000000000 : ℝ)*(major_s4_1) + (2173142677481/1000000000000 : ℝ)*(major_s4_2) + (1765773/500000000000 : ℝ)*(sp_s4_1) + (11621261/200000000000 : ℝ)*(sp_s4_9) + (1931841/100000000000 : ℝ)*(sp_s4_20) + (2560955764779/1000000000000 : ℝ)*(sp_s4_21) + (512190639873/200000000000 : ℝ)*(sp_s4_22) + (1280448829237/500000000000 : ℝ)*(sp_s4_23) + (401155607151/200000000000 : ℝ)*(sp_s4_27) + (710511704031/500000000000 : ℝ)*(f.failure) + (256095673091/100000000000 : ℝ)*(f.sum) + (141643721727741958873/296499237100000000000000000000000 : ℝ)*base62 + (5898528511145593/7757800000000000000000000000 : ℝ)*base65 + (2016989702729/47774375000000000000000000 : ℝ)*base66 + (3310479634750837/3878900000000000000000000000 : ℝ)*base68 + (79581149558049183661/151785235900000000000000000000000 : ℝ)*base71 + (127479659767769/244568750000000000000000000 : ℝ)*base72 + (79106926999887/191097500000000000000000000 : ℝ)*base74 + (3529379129245411/7826200000000000000000000000 : ℝ)*base77 + (40920446453856651023/149556725450000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (173/3125000000000000 : ℝ)*base87 + (173/3125000000000000 : ℝ)*base89 + (173/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((39131/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39131/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76439/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76439/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38789/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38789/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((67941/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67941/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4193/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4193/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13779/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13779/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305055_s4 p hpa hpb X hX hprev3

#print axioms solution

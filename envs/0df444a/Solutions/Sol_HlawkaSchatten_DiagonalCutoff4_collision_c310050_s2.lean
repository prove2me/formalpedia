-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310050_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:25:31.547249+00:00
-- url     : https://prove2.me/submissions/9443a90e-a778-46f7-bdcd-f18122c7d85d

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
theorem collision_support_c310050_s2_s2_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (926766449/2500000000 : ℝ)*x 0 + (-3600850399/10000000000 : ℝ)*x 1 + (-1347768069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (926766449/2500000000 : ℝ)^9 ≤ (27918757898421/100000000000000 : ℝ)^7 := by
    have hnat : (926766449 : ℕ)^9*100000000000000^7 ≤ 27918757898421^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926766449 2500000000 27918757898421 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3600850399/10000000000 : ℝ)^9 ≤ (3361814030783/12500000000000 : ℝ)^7 := by
    have hnat : (3600850399 : ℕ)^9*12500000000000^7 ≤ 3361814030783^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3600850399 10000000000 3361814030783 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347768069/2500000000 : ℝ)^9 ≤ (45186729844087/100000000000000 : ℝ)^7 := by
    have hnat : (1347768069 : ℕ)^9*100000000000000^7 ≤ 45186729844087^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347768069 2500000000 45186729844087 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(926766449/2500000000 : ℝ), (-3600850399/10000000000 : ℝ), (-1347768069/2500000000 : ℝ)] ![(27918757898421/100000000000000 : ℝ), (3361814030783/12500000000000 : ℝ), (45186729844087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(926766449/2500000000 : ℝ)|^9 ≤ (27918757898421/100000000000000 : ℝ)^7
        have hw : |(926766449/2500000000 : ℝ)|=(926766449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3600850399/10000000000 : ℝ)|^9 ≤ (3361814030783/12500000000000 : ℝ)^7
        have hw : |(-3600850399/10000000000 : ℝ)|=(3600850399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1347768069/2500000000 : ℝ)|^9 ≤ (45186729844087/100000000000000 : ℝ)^7
        have hw : |(-1347768069/2500000000 : ℝ)|=(1347768069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5764031079/10000000000 : ℝ)*x 0 + (2537959563/5000000000 : ℝ)*x 1 + (764157069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5764031079/10000000000 : ℝ)^9 ≤ (49245029673367/100000000000000 : ℝ)^7 := by
    have hnat : (5764031079 : ℕ)^9*100000000000000^7 ≤ 49245029673367^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5764031079 10000000000 49245029673367 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2537959563/5000000000 : ℝ)^9 ≤ (836384605707/2000000000000 : ℝ)^7 := by
    have hnat : (2537959563 : ℕ)^9*2000000000000^7 ≤ 836384605707^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537959563 5000000000 836384605707 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764157069/5000000000 : ℝ)^9 ≤ (8935740027963/100000000000000 : ℝ)^7 := by
    have hnat : (764157069 : ℕ)^9*100000000000000^7 ≤ 8935740027963^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764157069 5000000000 8935740027963 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5764031079/10000000000 : ℝ), (2537959563/5000000000 : ℝ), (764157069/5000000000 : ℝ)] ![(49245029673367/100000000000000 : ℝ), (836384605707/2000000000000 : ℝ), (8935740027963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5764031079/10000000000 : ℝ)|^9 ≤ (49245029673367/100000000000000 : ℝ)^7
        have hw : |(5764031079/10000000000 : ℝ)|=(5764031079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2537959563/5000000000 : ℝ)|^9 ≤ (836384605707/2000000000000 : ℝ)^7
        have hw : |(2537959563/5000000000 : ℝ)|=(2537959563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(764157069/5000000000 : ℝ)|^9 ≤ (8935740027963/100000000000000 : ℝ)^7
        have hw : |(764157069/5000000000 : ℝ)|=(764157069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (491746201/1250000000 : ℝ)*x 0 + (5900721523/10000000000 : ℝ)*x 1 + (-345107701/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491746201/1250000000 : ℝ)^9 ≤ (30134808026137/100000000000000 : ℝ)^7 := by
    have hnat : (491746201 : ℕ)^9*100000000000000^7 ≤ 30134808026137^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491746201 1250000000 30134808026137 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5900721523/10000000000 : ℝ)^9 ≤ (50751564999949/100000000000000 : ℝ)^7 := by
    have hnat : (5900721523 : ℕ)^9*100000000000000^7 ≤ 50751564999949^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5900721523 10000000000 50751564999949 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345107701/1250000000 : ℝ)^9 ≤ (9556813475769/50000000000000 : ℝ)^7 := by
    have hnat : (345107701 : ℕ)^9*50000000000000^7 ≤ 9556813475769^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345107701 1250000000 9556813475769 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(491746201/1250000000 : ℝ), (5900721523/10000000000 : ℝ), (-345107701/1250000000 : ℝ)] ![(30134808026137/100000000000000 : ℝ), (50751564999949/100000000000000 : ℝ), (9556813475769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(491746201/1250000000 : ℝ)|^9 ≤ (30134808026137/100000000000000 : ℝ)^7
        have hw : |(491746201/1250000000 : ℝ)|=(491746201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5900721523/10000000000 : ℝ)|^9 ≤ (50751564999949/100000000000000 : ℝ)^7
        have hw : |(5900721523/10000000000 : ℝ)|=(5900721523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-345107701/1250000000 : ℝ)|^9 ≤ (9556813475769/50000000000000 : ℝ)^7
        have hw : |(-345107701/1250000000 : ℝ)|=(345107701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1505892917/5000000000 : ℝ)*x 0 + (2638034503/10000000000 : ℝ)*x 1 + (-846654117/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1505892917/5000000000 : ℝ)^9 ≤ (21375519692571/100000000000000 : ℝ)^7 := by
    have hnat : (1505892917 : ℕ)^9*100000000000000^7 ≤ 21375519692571^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505892917 5000000000 21375519692571 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2638034503/10000000000 : ℝ)^9 ≤ (4506838994871/25000000000000 : ℝ)^7 := by
    have hnat : (2638034503 : ℕ)^9*25000000000000^7 ≤ 4506838994871^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638034503 10000000000 4506838994871 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846654117/1250000000 : ℝ)^9 ≤ (12119424862277/20000000000000 : ℝ)^7 := by
    have hnat : (846654117 : ℕ)^9*20000000000000^7 ≤ 12119424862277^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846654117 1250000000 12119424862277 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1505892917/5000000000 : ℝ), (2638034503/10000000000 : ℝ), (-846654117/1250000000 : ℝ)] ![(21375519692571/100000000000000 : ℝ), (4506838994871/25000000000000 : ℝ), (12119424862277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1505892917/5000000000 : ℝ)|^9 ≤ (21375519692571/100000000000000 : ℝ)^7
        have hw : |(-1505892917/5000000000 : ℝ)|=(1505892917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2638034503/10000000000 : ℝ)|^9 ≤ (4506838994871/25000000000000 : ℝ)^7
        have hw : |(2638034503/10000000000 : ℝ)|=(2638034503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-846654117/1250000000 : ℝ)|^9 ≤ (12119424862277/20000000000000 : ℝ)^7
        have hw : |(-846654117/1250000000 : ℝ)|=(846654117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3526080957/10000000000 : ℝ)*x 0 + (-3009976023/10000000000 : ℝ)*x 1 + (-3027427649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3526080957/10000000000 : ℝ)^9 ≤ (26178648156211/100000000000000 : ℝ)^7 := by
    have hnat : (3526080957 : ℕ)^9*100000000000000^7 ≤ 26178648156211^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3526080957 10000000000 26178648156211 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3009976023/10000000000 : ℝ)^9 ≤ (21359006425669/100000000000000 : ℝ)^7 := by
    have hnat : (3009976023 : ℕ)^9*100000000000000^7 ≤ 21359006425669^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3009976023 10000000000 21359006425669 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3027427649/5000000000 : ℝ)^9 ≤ (52462345411283/100000000000000 : ℝ)^7 := by
    have hnat : (3027427649 : ℕ)^9*100000000000000^7 ≤ 52462345411283^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3027427649 5000000000 52462345411283 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3526080957/10000000000 : ℝ), (-3009976023/10000000000 : ℝ), (-3027427649/5000000000 : ℝ)] ![(26178648156211/100000000000000 : ℝ), (21359006425669/100000000000000 : ℝ), (52462345411283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3526080957/10000000000 : ℝ)|^9 ≤ (26178648156211/100000000000000 : ℝ)^7
        have hw : |(3526080957/10000000000 : ℝ)|=(3526080957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3009976023/10000000000 : ℝ)|^9 ≤ (21359006425669/100000000000000 : ℝ)^7
        have hw : |(-3009976023/10000000000 : ℝ)|=(3009976023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3027427649/5000000000 : ℝ)|^9 ≤ (52462345411283/100000000000000 : ℝ)^7
        have hw : |(-3027427649/5000000000 : ℝ)|=(3027427649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2785886007/5000000000 : ℝ)*x 0 + (5684143103/10000000000 : ℝ)*x 1 + (894449001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2785886007/5000000000 : ℝ)^9 ≤ (9428660563407/20000000000000 : ℝ)^7 := by
    have hnat : (2785886007 : ℕ)^9*20000000000000^7 ≤ 9428660563407^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785886007 5000000000 9428660563407 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5684143103/10000000000 : ℝ)^9 ≤ (1934769716341/4000000000000 : ℝ)^7 := by
    have hnat : (5684143103 : ℕ)^9*4000000000000^7 ≤ 1934769716341^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684143103 10000000000 1934769716341 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894449001/10000000000 : ℝ)^9 ≤ (560931783561/12500000000000 : ℝ)^7 := by
    have hnat : (894449001 : ℕ)^9*12500000000000^7 ≤ 560931783561^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894449001 10000000000 560931783561 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2785886007/5000000000 : ℝ), (5684143103/10000000000 : ℝ), (894449001/10000000000 : ℝ)] ![(9428660563407/20000000000000 : ℝ), (1934769716341/4000000000000 : ℝ), (560931783561/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2785886007/5000000000 : ℝ)|^9 ≤ (9428660563407/20000000000000 : ℝ)^7
        have hw : |(2785886007/5000000000 : ℝ)|=(2785886007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5684143103/10000000000 : ℝ)|^9 ≤ (1934769716341/4000000000000 : ℝ)^7
        have hw : |(5684143103/10000000000 : ℝ)|=(5684143103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(894449001/10000000000 : ℝ)|^9 ≤ (560931783561/12500000000000 : ℝ)^7
        have hw : |(894449001/10000000000 : ℝ)|=(894449001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (177798599/500000000 : ℝ)*x 0 + (109710801/156250000 : ℝ)*x 1 + (-1676927673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (177798599/500000000 : ℝ)^9 ≤ (661607955779/2500000000000 : ℝ)^7 := by
    have hnat : (177798599 : ℕ)^9*2500000000000^7 ≤ 661607955779^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177798599 500000000 661607955779 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109710801/156250000 : ℝ)^9 ≤ (7933449234929/12500000000000 : ℝ)^7 := by
    have hnat : (109710801 : ℕ)^9*12500000000000^7 ≤ 7933449234929^7*156250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109710801 156250000 7933449234929 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1676927673/10000000000 : ℝ)^9 ≤ (5034043941291/50000000000000 : ℝ)^7 := by
    have hnat : (1676927673 : ℕ)^9*50000000000000^7 ≤ 5034043941291^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676927673 10000000000 5034043941291 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(177798599/500000000 : ℝ), (109710801/156250000 : ℝ), (-1676927673/10000000000 : ℝ)] ![(661607955779/2500000000000 : ℝ), (7933449234929/12500000000000 : ℝ), (5034043941291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(177798599/500000000 : ℝ)|^9 ≤ (661607955779/2500000000000 : ℝ)^7
        have hw : |(177798599/500000000 : ℝ)|=(177798599/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109710801/156250000 : ℝ)|^9 ≤ (7933449234929/12500000000000 : ℝ)^7
        have hw : |(109710801/156250000 : ℝ)|=(109710801/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1676927673/10000000000 : ℝ)|^9 ≤ (5034043941291/50000000000000 : ℝ)^7
        have hw : |(-1676927673/10000000000 : ℝ)|=(1676927673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1344384973/5000000000 : ℝ)*x 0 + (2930480427/10000000000 : ℝ)*x 1 + (-1699652329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344384973/5000000000 : ℝ)^9 ≤ (4618585427721/25000000000000 : ℝ)^7 := by
    have hnat : (1344384973 : ℕ)^9*25000000000000^7 ≤ 4618585427721^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344384973 5000000000 4618585427721 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2930480427/10000000000 : ℝ)^9 ≤ (10318240267623/50000000000000 : ℝ)^7 := by
    have hnat : (2930480427 : ℕ)^9*50000000000000^7 ≤ 10318240267623^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2930480427 10000000000 10318240267623 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1699652329/2500000000 : ℝ)^9 ≤ (30444588872841/50000000000000 : ℝ)^7 := by
    have hnat : (1699652329 : ℕ)^9*50000000000000^7 ≤ 30444588872841^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699652329 2500000000 30444588872841 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1344384973/5000000000 : ℝ), (2930480427/10000000000 : ℝ), (-1699652329/2500000000 : ℝ)] ![(4618585427721/25000000000000 : ℝ), (10318240267623/50000000000000 : ℝ), (30444588872841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1344384973/5000000000 : ℝ)|^9 ≤ (4618585427721/25000000000000 : ℝ)^7
        have hw : |(-1344384973/5000000000 : ℝ)|=(1344384973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2930480427/10000000000 : ℝ)|^9 ≤ (10318240267623/50000000000000 : ℝ)^7
        have hw : |(2930480427/10000000000 : ℝ)|=(2930480427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1699652329/2500000000 : ℝ)|^9 ≤ (30444588872841/50000000000000 : ℝ)^7
        have hw : |(-1699652329/2500000000 : ℝ)|=(1699652329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1572313887/5000000000 : ℝ)*x 0 + (-1726456967/5000000000 : ℝ)*x 1 + (-6006332251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1572313887/5000000000 : ℝ)^9 ≤ (141220459153/625000000000 : ℝ)^7 := by
    have hnat : (1572313887 : ℕ)^9*625000000000^7 ≤ 141220459153^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572313887 5000000000 141220459153 625000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1726456967/5000000000 : ℝ)^9 ≤ (3185288978141/12500000000000 : ℝ)^7 := by
    have hnat : (1726456967 : ℕ)^9*12500000000000^7 ≤ 3185288978141^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726456967 5000000000 3185288978141 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6006332251/10000000000 : ℝ)^9 ≤ (25961207350167/50000000000000 : ℝ)^7 := by
    have hnat : (6006332251 : ℕ)^9*50000000000000^7 ≤ 25961207350167^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6006332251 10000000000 25961207350167 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1572313887/5000000000 : ℝ), (-1726456967/5000000000 : ℝ), (-6006332251/10000000000 : ℝ)] ![(141220459153/625000000000 : ℝ), (3185288978141/12500000000000 : ℝ), (25961207350167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1572313887/5000000000 : ℝ)|^9 ≤ (141220459153/625000000000 : ℝ)^7
        have hw : |(1572313887/5000000000 : ℝ)|=(1572313887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1726456967/5000000000 : ℝ)|^9 ≤ (3185288978141/12500000000000 : ℝ)^7
        have hw : |(-1726456967/5000000000 : ℝ)|=(1726456967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6006332251/10000000000 : ℝ)|^9 ≤ (25961207350167/50000000000000 : ℝ)^7
        have hw : |(-6006332251/10000000000 : ℝ)|=(6006332251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1574300173/2500000000 : ℝ)*x 0 + (981042703/2000000000 : ℝ)*x 1 + (471486961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1574300173/2500000000 : ℝ)^9 ≤ (13794346297797/25000000000000 : ℝ)^7 := by
    have hnat : (1574300173 : ℕ)^9*25000000000000^7 ≤ 13794346297797^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1574300173 2500000000 13794346297797 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981042703/2000000000 : ℝ)^9 ≤ (40019758509487/100000000000000 : ℝ)^7 := by
    have hnat : (981042703 : ℕ)^9*100000000000000^7 ≤ 40019758509487^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981042703 2000000000 40019758509487 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471486961/5000000000 : ℝ)^9 ≤ (2401428143721/50000000000000 : ℝ)^7 := by
    have hnat : (471486961 : ℕ)^9*50000000000000^7 ≤ 2401428143721^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471486961 5000000000 2401428143721 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1574300173/2500000000 : ℝ), (981042703/2000000000 : ℝ), (471486961/5000000000 : ℝ)] ![(13794346297797/25000000000000 : ℝ), (40019758509487/100000000000000 : ℝ), (2401428143721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1574300173/2500000000 : ℝ)|^9 ≤ (13794346297797/25000000000000 : ℝ)^7
        have hw : |(1574300173/2500000000 : ℝ)|=(1574300173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(981042703/2000000000 : ℝ)|^9 ≤ (40019758509487/100000000000000 : ℝ)^7
        have hw : |(981042703/2000000000 : ℝ)|=(981042703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(471486961/5000000000 : ℝ)|^9 ≤ (2401428143721/50000000000000 : ℝ)^7
        have hw : |(471486961/5000000000 : ℝ)|=(471486961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1047255813/2000000000 : ℝ)*x 0 + (5544080713/10000000000 : ℝ)*x 1 + (-405047353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047255813/2000000000 : ℝ)^9 ≤ (21762740512137/50000000000000 : ℝ)^7 := by
    have hnat : (1047255813 : ℕ)^9*50000000000000^7 ≤ 21762740512137^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047255813 2000000000 21762740512137 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5544080713/10000000000 : ℝ)^9 ≤ (936845513191/2000000000000 : ℝ)^7 := by
    have hnat : (5544080713 : ℕ)^9*2000000000000^7 ≤ 936845513191^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5544080713 10000000000 936845513191 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405047353/2500000000 : ℝ)^9 ≤ (9632243301311/100000000000000 : ℝ)^7 := by
    have hnat : (405047353 : ℕ)^9*100000000000000^7 ≤ 9632243301311^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405047353 2500000000 9632243301311 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047255813/2000000000 : ℝ), (5544080713/10000000000 : ℝ), (-405047353/2500000000 : ℝ)] ![(21762740512137/50000000000000 : ℝ), (936845513191/2000000000000 : ℝ), (9632243301311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047255813/2000000000 : ℝ)|^9 ≤ (21762740512137/50000000000000 : ℝ)^7
        have hw : |(1047255813/2000000000 : ℝ)|=(1047255813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5544080713/10000000000 : ℝ)|^9 ≤ (936845513191/2000000000000 : ℝ)^7
        have hw : |(5544080713/10000000000 : ℝ)|=(5544080713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-405047353/2500000000 : ℝ)|^9 ≤ (9632243301311/100000000000000 : ℝ)^7
        have hw : |(-405047353/2500000000 : ℝ)|=(405047353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3242108583/10000000000 : ℝ)*x 0 + (1584921441/5000000000 : ℝ)*x 1 + (-6163140823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3242108583/10000000000 : ℝ)^9 ≤ (23499791035799/100000000000000 : ℝ)^7 := by
    have hnat : (3242108583 : ℕ)^9*100000000000000^7 ≤ 23499791035799^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3242108583 10000000000 23499791035799 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1584921441/5000000000 : ℝ)^9 ≤ (1426780308539/6250000000000 : ℝ)^7 := by
    have hnat : (1584921441 : ℕ)^9*6250000000000^7 ≤ 1426780308539^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584921441 5000000000 1426780308539 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6163140823/10000000000 : ℝ)^9 ≤ (53671724022001/100000000000000 : ℝ)^7 := by
    have hnat : (6163140823 : ℕ)^9*100000000000000^7 ≤ 53671724022001^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6163140823 10000000000 53671724022001 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3242108583/10000000000 : ℝ), (1584921441/5000000000 : ℝ), (-6163140823/10000000000 : ℝ)] ![(23499791035799/100000000000000 : ℝ), (1426780308539/6250000000000 : ℝ), (53671724022001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3242108583/10000000000 : ℝ)|^9 ≤ (23499791035799/100000000000000 : ℝ)^7
        have hw : |(-3242108583/10000000000 : ℝ)|=(3242108583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1584921441/5000000000 : ℝ)|^9 ≤ (1426780308539/6250000000000 : ℝ)^7
        have hw : |(1584921441/5000000000 : ℝ)|=(1584921441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6163140823/10000000000 : ℝ)|^9 ≤ (53671724022001/100000000000000 : ℝ)^7
        have hw : |(-6163140823/10000000000 : ℝ)|=(6163140823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1841000559/5000000000 : ℝ)*x 0 + (-3565714231/10000000000 : ℝ)*x 1 + (-108895227/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1841000559/5000000000 : ℝ)^9 ≤ (13838145619159/50000000000000 : ℝ)^7 := by
    have hnat : (1841000559 : ℕ)^9*50000000000000^7 ≤ 13838145619159^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841000559 5000000000 13838145619159 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3565714231/10000000000 : ℝ)^9 ≤ (1327878703103/5000000000000 : ℝ)^7 := by
    have hnat : (3565714231 : ℕ)^9*5000000000000^7 ≤ 1327878703103^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3565714231 10000000000 1327878703103 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108895227/200000000 : ℝ)^9 ≤ (45766134679589/100000000000000 : ℝ)^7 := by
    have hnat : (108895227 : ℕ)^9*100000000000000^7 ≤ 45766134679589^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108895227 200000000 45766134679589 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1841000559/5000000000 : ℝ), (-3565714231/10000000000 : ℝ), (-108895227/200000000 : ℝ)] ![(13838145619159/50000000000000 : ℝ), (1327878703103/5000000000000 : ℝ), (45766134679589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1841000559/5000000000 : ℝ)|^9 ≤ (13838145619159/50000000000000 : ℝ)^7
        have hw : |(1841000559/5000000000 : ℝ)|=(1841000559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3565714231/10000000000 : ℝ)|^9 ≤ (1327878703103/5000000000000 : ℝ)^7
        have hw : |(-3565714231/10000000000 : ℝ)|=(3565714231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108895227/200000000 : ℝ)|^9 ≤ (45766134679589/100000000000000 : ℝ)^7
        have hw : |(-108895227/200000000 : ℝ)|=(108895227/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6550616573/10000000000 : ℝ)*x 0 + (4407698191/10000000000 : ℝ)*x 1 + (318554541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6550616573/10000000000 : ℝ)^9 ≤ (58048549717293/100000000000000 : ℝ)^7 := by
    have hnat : (6550616573 : ℕ)^9*100000000000000^7 ≤ 58048549717293^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6550616573 10000000000 58048549717293 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4407698191/10000000000 : ℝ)^9 ≤ (17439261758117/50000000000000 : ℝ)^7 := by
    have hnat : (4407698191 : ℕ)^9*50000000000000^7 ≤ 17439261758117^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407698191 10000000000 17439261758117 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318554541/2500000000 : ℝ)^9 ≤ (3536463377687/50000000000000 : ℝ)^7 := by
    have hnat : (318554541 : ℕ)^9*50000000000000^7 ≤ 3536463377687^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318554541 2500000000 3536463377687 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6550616573/10000000000 : ℝ), (4407698191/10000000000 : ℝ), (318554541/2500000000 : ℝ)] ![(58048549717293/100000000000000 : ℝ), (17439261758117/50000000000000 : ℝ), (3536463377687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6550616573/10000000000 : ℝ)|^9 ≤ (58048549717293/100000000000000 : ℝ)^7
        have hw : |(6550616573/10000000000 : ℝ)|=(6550616573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4407698191/10000000000 : ℝ)|^9 ≤ (17439261758117/50000000000000 : ℝ)^7
        have hw : |(4407698191/10000000000 : ℝ)|=(4407698191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318554541/2500000000 : ℝ)|^9 ≤ (3536463377687/50000000000000 : ℝ)^7
        have hw : |(318554541/2500000000 : ℝ)|=(318554541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310050_s2_s2_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1115498019/5000000000 : ℝ)*x 0 + (7443843589/10000000000 : ℝ)*x 1 + (-2526039051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115498019/5000000000 : ℝ)^9 ≤ (7266505441089/50000000000000 : ℝ)^7 := by
    have hnat : (1115498019 : ℕ)^9*50000000000000^7 ≤ 7266505441089^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115498019 5000000000 7266505441089 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7443843589/10000000000 : ℝ)^9 ≤ (2736704272309/4000000000000 : ℝ)^7 := by
    have hnat : (7443843589 : ℕ)^9*4000000000000^7 ≤ 2736704272309^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7443843589 10000000000 2736704272309 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2526039051/10000000000 : ℝ)^9 ≤ (8524691144507/50000000000000 : ℝ)^7 := by
    have hnat : (2526039051 : ℕ)^9*50000000000000^7 ≤ 8524691144507^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526039051 10000000000 8524691144507 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1115498019/5000000000 : ℝ), (7443843589/10000000000 : ℝ), (-2526039051/10000000000 : ℝ)] ![(7266505441089/50000000000000 : ℝ), (2736704272309/4000000000000 : ℝ), (8524691144507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1115498019/5000000000 : ℝ)|^9 ≤ (7266505441089/50000000000000 : ℝ)^7
        have hw : |(1115498019/5000000000 : ℝ)|=(1115498019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7443843589/10000000000 : ℝ)|^9 ≤ (2736704272309/4000000000000 : ℝ)^7
        have hw : |(7443843589/10000000000 : ℝ)|=(7443843589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2526039051/10000000000 : ℝ)|^9 ≤ (8524691144507/50000000000000 : ℝ)^7
        have hw : |(-2526039051/10000000000 : ℝ)|=(2526039051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310050_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((17987/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17987/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61833/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61833/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-48333/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-48333/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8879/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8879/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1009/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1009/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-7461/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-7461/50000 : ℝ)*X 1 2) := by
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
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (17987/25000 : ℝ) ^ (35/8 : ℝ) ≤ (23684102185624890481/100000000000000000000 : ℝ) := by
    have hpowers : (17987/25000 : ℝ)^35 ≤ (23684102185624890481/100000000000000000000 : ℝ)^8 := by
      have hnat : (17987 : ℕ)^35*100000000000000000000^8 ≤ 23684102185624890481^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17987 25000 23684102185624890481 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17987/25000 : ℝ)) (X := (23684102185624890481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (123684102185624890481/100000000000000000000 : ℝ) ≤ (419913954203763/400000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (123684102185624890481/100000000000000000000 : ℝ)^8 ≤ (419913954203763/400000000000000 : ℝ)^35 := by
      have hnat : (123684102185624890481 : ℕ)^8*400000000000000^35 ≤ 419913954203763^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123684102185624890481 100000000000000000000 419913954203763 400000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (419913954203763/400000000000000 : ℝ)) (X := (123684102185624890481/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (73684102185624890481/50000000000000000000 : ℝ) ≤ (2185356484095841/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (73684102185624890481/50000000000000000000 : ℝ)^8 ≤ (2185356484095841/2000000000000000 : ℝ)^35 := by
      have hnat : (73684102185624890481 : ℕ)^8*2000000000000000^35 ≤ 2185356484095841^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73684102185624890481 50000000000000000000 2185356484095841 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2185356484095841/2000000000000000 : ℝ)) (X := (73684102185624890481/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19913954203763/287792000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(42893356538513/719480000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (17987/25000 : ℝ)) (alpha := (19913954203763/287792000000000 : ℝ)) (beta := (42893356538513/719480000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17987/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19913954203763/287792000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(42893356538513/719480000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (61833/100000 : ℝ) ^ (35/8 : ℝ) ≤ (76290227268395003/625000000000000000 : ℝ) := by
    have hpowers : (61833/100000 : ℝ)^35 ≤ (76290227268395003/625000000000000000 : ℝ)^8 := by
      have hnat : (61833 : ℕ)^35*625000000000000000^8 ≤ 76290227268395003^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61833 100000 76290227268395003 625000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61833/100000 : ℝ)) (X := (76290227268395003/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (701290227268395003/625000000000000000 : ℝ) ≤ (1026674163509149/1000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (701290227268395003/625000000000000000 : ℝ)^8 ≤ (1026674163509149/1000000000000000 : ℝ)^35 := by
      have hnat : (701290227268395003 : ℕ)^8*1000000000000000^35 ≤ 1026674163509149^35*625000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701290227268395003 625000000000000000 1026674163509149 1000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1026674163509149/1000000000000000 : ℝ)) (X := (701290227268395003/625000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (388790227268395003/312500000000000000 : ℝ) ≤ (2627988799754543/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (388790227268395003/312500000000000000 : ℝ)^8 ≤ (2627988799754543/2500000000000000 : ℝ)^35 := by
      have hnat : (388790227268395003 : ℕ)^8*2500000000000000^35 ≤ 2627988799754543^35*312500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        388790227268395003 312500000000000000 2627988799754543 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2627988799754543/2500000000000000 : ℝ)) (X := (388790227268395003/312500000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(8891387836383/206110000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(122606781963341/3091650000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (61833/100000 : ℝ)) (alpha := (8891387836383/206110000000000 : ℝ)) (beta := (122606781963341/3091650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (61833/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(8891387836383/206110000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(122606781963341/3091650000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (48333/100000 : ℝ) ^ (35/8 : ℝ) ≤ (4154955880915100521/100000000000000000000 : ℝ) := by
    have hpowers : (48333/100000 : ℝ)^35 ≤ (4154955880915100521/100000000000000000000 : ℝ)^8 := by
      have hnat : (48333 : ℕ)^35*100000000000000000000^8 ≤ 4154955880915100521^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48333 100000 4154955880915100521 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48333/100000 : ℝ)) (X := (4154955880915100521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (104154955880915100521/100000000000000000000 : ℝ) ≤ (5046742349283601/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (104154955880915100521/100000000000000000000 : ℝ)^8 ≤ (5046742349283601/5000000000000000 : ℝ)^35 := by
      have hnat : (104154955880915100521 : ℕ)^8*5000000000000000^35 ≤ 5046742349283601^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104154955880915100521 100000000000000000000 5046742349283601 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5046742349283601/5000000000000000 : ℝ)) (X := (104154955880915100521/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (54154955880915100521/50000000000000000000 : ℝ) ≤ (127301691254597/125000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (54154955880915100521/50000000000000000000 : ℝ)^8 ≤ (127301691254597/125000000000000 : ℝ)^35 := by
      have hnat : (54154955880915100521 : ℕ)^8*125000000000000^35 ≤ 127301691254597^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54154955880915100521 50000000000000000000 127301691254597 125000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (127301691254597/125000000000000 : ℝ)) (X := (54154955880915100521/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(46742349283601/2416650000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(45325300900279/2416650000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (48333/100000 : ℝ)) (alpha := (46742349283601/2416650000000000 : ℝ)) (beta := (45325300900279/2416650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (48333/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(46742349283601/2416650000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(45325300900279/2416650000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((926766449/2500000000 : ℝ)*X 1 0+(-3600850399/10000000000 : ℝ)*X 1 1+(-1347768069/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5764031079/10000000000 : ℝ)*X 2 0+(2537959563/5000000000 : ℝ)*X 2 1+(764157069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((491746201/1250000000 : ℝ)*X 0 0+(5900721523/10000000000 : ℝ)*X 0 1+(-345107701/1250000000 : ℝ)*X 0 2+(491746201/1250000000 : ℝ)*X 1 0+(5900721523/10000000000 : ℝ)*X 1 1+(-345107701/1250000000 : ℝ)*X 1 2+(491746201/1250000000 : ℝ)*X 2 0+(5900721523/10000000000 : ℝ)*X 2 1+(-345107701/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1505892917/5000000000 : ℝ)*X 0 0+(2638034503/10000000000 : ℝ)*X 0 1+(-846654117/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((3526080957/10000000000 : ℝ)*X 1 0+(-3009976023/10000000000 : ℝ)*X 1 1+(-3027427649/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2785886007/5000000000 : ℝ)*X 2 0+(5684143103/10000000000 : ℝ)*X 2 1+(894449001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((177798599/500000000 : ℝ)*X 0 0+(109710801/156250000 : ℝ)*X 0 1+(-1676927673/10000000000 : ℝ)*X 0 2+(177798599/500000000 : ℝ)*X 1 0+(109710801/156250000 : ℝ)*X 1 1+(-1676927673/10000000000 : ℝ)*X 1 2+(177798599/500000000 : ℝ)*X 2 0+(109710801/156250000 : ℝ)*X 2 1+(-1676927673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1344384973/5000000000 : ℝ)*X 0 0+(2930480427/10000000000 : ℝ)*X 0 1+(-1699652329/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1572313887/5000000000 : ℝ)*X 1 0+(-1726456967/5000000000 : ℝ)*X 1 1+(-6006332251/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1574300173/2500000000 : ℝ)*X 2 0+(981042703/2000000000 : ℝ)*X 2 1+(471486961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1047255813/2000000000 : ℝ)*X 0 0+(5544080713/10000000000 : ℝ)*X 0 1+(-405047353/2500000000 : ℝ)*X 0 2+(1047255813/2000000000 : ℝ)*X 1 0+(5544080713/10000000000 : ℝ)*X 1 1+(-405047353/2500000000 : ℝ)*X 1 2+(1047255813/2000000000 : ℝ)*X 2 0+(5544080713/10000000000 : ℝ)*X 2 1+(-405047353/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-3242108583/10000000000 : ℝ)*X 0 0+(1584921441/5000000000 : ℝ)*X 0 1+(-6163140823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1841000559/5000000000 : ℝ)*X 1 0+(-3565714231/10000000000 : ℝ)*X 1 1+(-108895227/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((6550616573/10000000000 : ℝ)*X 2 0+(4407698191/10000000000 : ℝ)*X 2 1+(318554541/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1115498019/5000000000 : ℝ)*X 0 0+(7443843589/10000000000 : ℝ)*X 0 1+(-2526039051/10000000000 : ℝ)*X 0 2+(1115498019/5000000000 : ℝ)*X 1 0+(7443843589/10000000000 : ℝ)*X 1 1+(-2526039051/10000000000 : ℝ)*X 1 2+(1115498019/5000000000 : ℝ)*X 2 0+(7443843589/10000000000 : ℝ)*X 2 1+(-2526039051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310050_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((8879/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8879/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16241024072216512385878067951407/1194566389665400000000000000000000000 : ℝ) := by norm_num
    linear_combination (790213/1000000000000 : ℝ)*(base49) + (1443621/250000000000 : ℝ)*(base59) + (366323187611/250000000000 : ℝ)*(base60) + (6653788158707/1000000000000 : ℝ)*(major_s2_0) + (6653788158707/1000000000000 : ℝ)*(major_s2_1) + (6653788158707/1000000000000 : ℝ)*(major_s2_2) + (3682607/62500000000 : ℝ)*(sp_s2_2) + (9195040242897/1000000000000 : ℝ)*(sp_s2_7) + (2298723973011/250000000000 : ℝ)*(sp_s2_8) + (1838996264237/200000000000 : ℝ)*(sp_s2_9) + (514060392367/125000000000 : ℝ)*(sp_s2_13) + (129516797/1000000000000 : ℝ)*(sp_s2_15) + (1854257/125000000000 : ℝ)*(sp_s2_22) + (48403657/1000000000000 : ℝ)*(sp_s2_27) + (64258305353/15625000000 : ℝ)*(f.failure) + (9195040242897/1000000000000 : ℝ)*(f.sum) + (230427878324389549/1556549160937500000000000000000 : ℝ)*base63 + (317219102961967/2416650000000000000000000000 : ℝ)*base64 + (32924914197023/193228125000000000000000000 : ℝ)*base67 + (1093165745077493/2416650000000000000000000000 : ℝ)*base69 + (141217253495285929027/347746268400000000000000000000000 : ℝ)*base70 + (147069468139397/719480000000000000000000000 : ℝ)*base72 + (36602066097457/206110000000000000000000000 : ℝ)*base75 + (70694016936019/1438960000000000000000000000 : ℝ)*base76 + (111809279249026203019/222438034200000000000000000000000 : ℝ)*base79 + (3517/3125000000000000 : ℝ)*base86 + (3517/3125000000000000 : ℝ)*base88 + (3517/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1009/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1009/3125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6015728780313084044669955433149/597283194832700000000000000000000000 : ℝ) := by norm_num
    linear_combination (67755326717/1000000000000 : ℝ)*(base39) + (1333067/500000000000 : ℝ)*(base59) + (1475858251097/1000000000000 : ℝ)*(base60) + (6634472639331/1000000000000 : ℝ)*(major_s2_0) + (6634472639331/1000000000000 : ℝ)*(major_s2_1) + (6634472639331/1000000000000 : ℝ)*(major_s2_2) + (5754221/250000000000 : ℝ)*(sp_s2_6) + (1779681/25000000000 : ℝ)*(sp_s2_8) + (9168348793543/1000000000000 : ℝ)*(sp_s2_14) + (4584114250931/500000000000 : ℝ)*(sp_s2_15) + (9168262158531/1000000000000 : ℝ)*(sp_s2_16) + (4100570110959/1000000000000 : ℝ)*(sp_s2_20) + (49104441/1000000000000 : ℝ)*(sp_s2_22) + (21658753/250000000000 : ℝ)*(sp_s2_23) + (4100593127843/1000000000000 : ℝ)*(f.failure) + (9168348793543/1000000000000 : ℝ)*(f.sum) + (3869624463412236523/16603191050000000000000000000000 : ℝ)*base63 + (436432304374983/805550000000000000000000000 : ℝ)*base65 + (23781655168283/1030550000000000000000000000 : ℝ)*base67 + (31399164690577/201387500000000000000000000 : ℝ)*base69 + (72490773015860779143/115915422800000000000000000000000 : ℝ)*base71 + (364501060208579/719480000000000000000000000 : ℝ)*base73 + (952254889339/25763750000000000000000000 : ℝ)*base74 + (105513991714211/1438960000000000000000000000 : ℝ)*base76 + (34983921879062771129/74146011400000000000000000000000 : ℝ)*base79 + (2499/100000000000000000 : ℝ)*base87 + (2499/100000000000000000 : ℝ)*base89 + (2499/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-7461/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-7461/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9293391743827438737113617036509/597283194832700000000000000000000000 : ℝ) := by norm_num
    linear_combination (348087/50000000000 : ℝ)*(base39) + (93473/500000000000 : ℝ)*(base49) + (28273419451/50000000000 : ℝ)*(base60) + (2343947695959/500000000000 : ℝ)*(major_s2_0) + (2343947695959/500000000000 : ℝ)*(major_s2_1) + (2343947695959/500000000000 : ℝ)*(major_s2_2) + (364726857/200000000000 : ℝ)*(sp_s2_1) + (2109199/31250000000 : ℝ)*(sp_s2_2) + (1037263/20000000000 : ℝ)*(sp_s2_8) + (4364491/62500000000 : ℝ)*(sp_s2_13) + (6478320693481/1000000000000 : ℝ)*(sp_s2_21) + (3238222598023/500000000000 : ℝ)*(sp_s2_22) + (6478253199113/1000000000000 : ℝ)*(sp_s2_23) + (2897395072013/1000000000000 : ℝ)*(sp_s2_27) + (289746490387/100000000000 : ℝ)*(f.failure) + (6478320693481/1000000000000 : ℝ)*(f.sum) + (2311419271829454249/16603191050000000000000000000000 : ℝ)*base63 + (448836313458309/805550000000000000000000000 : ℝ)*base65 + (2935550304721/4025585937500000000000000 : ℝ)*base66 + (102016196324217/402775000000000000000000000 : ℝ)*base69 + (25687198804131828227/57957711400000000000000000000000 : ℝ)*base71 + (66206317744519/359740000000000000000000000 : ℝ)*base72 + (59837871671449/206110000000000000000000000 : ℝ)*base75 + (465807660559369/719480000000000000000000000 : ℝ)*base77 + (19589254109354080869/37073005700000000000000000000000 : ℝ)*base78 + (3891/10000000000000000 : ℝ)*base87 + (3891/10000000000000000 : ℝ)*base89 + (3891/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((17987/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17987/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61833/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61833/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-48333/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-48333/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8879/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8879/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1009/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1009/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-7461/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-7461/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310050_s2 p hpa hpb X hX hprev1

#print axioms solution

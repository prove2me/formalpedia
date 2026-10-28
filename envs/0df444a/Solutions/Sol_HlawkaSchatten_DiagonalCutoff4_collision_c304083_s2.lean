-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304083_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:50:05.359291+00:00
-- url     : https://prove2.me/submissions/43bff98c-bbbb-4fb2-aeb0-6592e5e6427a

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
theorem collision_support_c304083_s2_s2_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3713667873/10000000000 : ℝ)*x 0 + (82445863/125000000 : ℝ)*x 1 + (-1187309233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3713667873/10000000000 : ℝ)^133 ≤ (271333264613/1000000000000 : ℝ)^101 := by
    have hnat : (3713667873 : ℕ)^133*1000000000000^101 ≤ 271333264613^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713667873 10000000000 271333264613 1000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82445863/125000000 : ℝ)^133 ≤ (28904425283719/50000000000000 : ℝ)^101 := by
    have hnat : (82445863 : ℕ)^133*50000000000000^101 ≤ 28904425283719^101*125000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82445863 125000000 28904425283719 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1187309233/5000000000 : ℝ)^133 ≤ (301156458939/2000000000000 : ℝ)^101 := by
    have hnat : (1187309233 : ℕ)^133*2000000000000^101 ≤ 301156458939^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187309233 5000000000 301156458939 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3713667873/10000000000 : ℝ), (82445863/125000000 : ℝ), (-1187309233/5000000000 : ℝ)] ![(271333264613/1000000000000 : ℝ), (28904425283719/50000000000000 : ℝ), (301156458939/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3713667873/10000000000 : ℝ)|^133 ≤ (271333264613/1000000000000 : ℝ)^101
        have hw : |(3713667873/10000000000 : ℝ)|=(3713667873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82445863/125000000 : ℝ)|^133 ≤ (28904425283719/50000000000000 : ℝ)^101
        have hw : |(82445863/125000000 : ℝ)|=(82445863/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1187309233/5000000000 : ℝ)|^133 ≤ (301156458939/2000000000000 : ℝ)^101
        have hw : |(-1187309233/5000000000 : ℝ)|=(1187309233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (643083173/2000000000 : ℝ)*x 0 + (4711687653/10000000000 : ℝ)*x 1 + (5027593647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643083173/2000000000 : ℝ)^133 ≤ (22444723889889/100000000000000 : ℝ)^101 := by
    have hnat : (643083173 : ℕ)^133*100000000000000^101 ≤ 22444723889889^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643083173 2000000000 22444723889889 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4711687653/10000000000 : ℝ)^133 ≤ (37121750761301/100000000000000 : ℝ)^101 := by
    have hnat : (4711687653 : ℕ)^133*100000000000000^101 ≤ 37121750761301^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4711687653 10000000000 37121750761301 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5027593647/10000000000 : ℝ)^133 ≤ (8086705066177/20000000000000 : ℝ)^101 := by
    have hnat : (5027593647 : ℕ)^133*20000000000000^101 ≤ 8086705066177^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027593647 10000000000 8086705066177 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(643083173/2000000000 : ℝ), (4711687653/10000000000 : ℝ), (5027593647/10000000000 : ℝ)] ![(22444723889889/100000000000000 : ℝ), (37121750761301/100000000000000 : ℝ), (8086705066177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(643083173/2000000000 : ℝ)|^133 ≤ (22444723889889/100000000000000 : ℝ)^101
        have hw : |(643083173/2000000000 : ℝ)|=(643083173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4711687653/10000000000 : ℝ)|^133 ≤ (37121750761301/100000000000000 : ℝ)^101
        have hw : |(4711687653/10000000000 : ℝ)|=(4711687653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5027593647/10000000000 : ℝ)|^133 ≤ (8086705066177/20000000000000 : ℝ)^101
        have hw : |(5027593647/10000000000 : ℝ)|=(5027593647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081560139/5000000000 : ℝ)*x 0 + (5001699777/10000000000 : ℝ)*x 1 + (5592799759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081560139/5000000000 : ℝ)^133 ≤ (13317207222863/100000000000000 : ℝ)^101 := by
    have hnat : (1081560139 : ℕ)^133*100000000000000^101 ≤ 13317207222863^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081560139 5000000000 13317207222863 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001699777/10000000000 : ℝ)^133 ≤ (1254985103377/3125000000000 : ℝ)^101 := by
    have hnat : (5001699777 : ℕ)^133*3125000000000^101 ≤ 1254985103377^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001699777 10000000000 1254985103377 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5592799759/10000000000 : ℝ)^133 ≤ (11630817360877/25000000000000 : ℝ)^101 := by
    have hnat : (5592799759 : ℕ)^133*25000000000000^101 ≤ 11630817360877^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592799759 10000000000 11630817360877 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081560139/5000000000 : ℝ), (5001699777/10000000000 : ℝ), (5592799759/10000000000 : ℝ)] ![(13317207222863/100000000000000 : ℝ), (1254985103377/3125000000000 : ℝ), (11630817360877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081560139/5000000000 : ℝ)|^133 ≤ (13317207222863/100000000000000 : ℝ)^101
        have hw : |(-1081560139/5000000000 : ℝ)|=(1081560139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001699777/10000000000 : ℝ)|^133 ≤ (1254985103377/3125000000000 : ℝ)^101
        have hw : |(5001699777/10000000000 : ℝ)|=(5001699777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5592799759/10000000000 : ℝ)|^133 ≤ (11630817360877/25000000000000 : ℝ)^101
        have hw : |(5592799759/10000000000 : ℝ)|=(5592799759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (25504981/40000000 : ℝ)*x 0 + (1894841/1000000000 : ℝ)*x 1 + (2712048479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25504981/40000000 : ℝ)^133 ≤ (11057959953309/20000000000000 : ℝ)^101 := by
    have hnat : (25504981 : ℕ)^133*20000000000000^101 ≤ 11057959953309^101*40000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25504981 40000000 11057959953309 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1894841/1000000000 : ℝ)^133 ≤ (6500721811/25000000000000 : ℝ)^101 := by
    have hnat : (1894841 : ℕ)^133*25000000000000^101 ≤ 6500721811^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894841 1000000000 6500721811 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712048479/5000000000 : ℝ)^133 ≤ (44684197334147/100000000000000 : ℝ)^101 := by
    have hnat : (2712048479 : ℕ)^133*100000000000000^101 ≤ 44684197334147^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712048479 5000000000 44684197334147 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(25504981/40000000 : ℝ), (1894841/1000000000 : ℝ), (2712048479/5000000000 : ℝ)] ![(11057959953309/20000000000000 : ℝ), (6500721811/25000000000000 : ℝ), (44684197334147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(25504981/40000000 : ℝ)|^133 ≤ (11057959953309/20000000000000 : ℝ)^101
        have hw : |(25504981/40000000 : ℝ)|=(25504981/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1894841/1000000000 : ℝ)|^133 ≤ (6500721811/25000000000000 : ℝ)^101
        have hw : |(1894841/1000000000 : ℝ)|=(1894841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712048479/5000000000 : ℝ)|^133 ≤ (44684197334147/100000000000000 : ℝ)^101
        have hw : |(2712048479/5000000000 : ℝ)|=(2712048479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (297044867/1000000000 : ℝ)*x 0 + (3858933763/5000000000 : ℝ)*x 1 + (-1563119377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (297044867/1000000000 : ℝ)^133 ≤ (20220662267271/100000000000000 : ℝ)^101 := by
    have hnat : (297044867 : ℕ)^133*100000000000000^101 ≤ 20220662267271^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297044867 1000000000 20220662267271 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3858933763/5000000000 : ℝ)^133 ≤ (71097266942401/100000000000000 : ℝ)^101 := by
    have hnat : (3858933763 : ℕ)^133*100000000000000^101 ≤ 71097266942401^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3858933763 5000000000 71097266942401 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1563119377/10000000000 : ℝ)^133 ≤ (4341035389401/50000000000000 : ℝ)^101 := by
    have hnat : (1563119377 : ℕ)^133*50000000000000^101 ≤ 4341035389401^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1563119377 10000000000 4341035389401 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(297044867/1000000000 : ℝ), (3858933763/5000000000 : ℝ), (-1563119377/10000000000 : ℝ)] ![(20220662267271/100000000000000 : ℝ), (71097266942401/100000000000000 : ℝ), (4341035389401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(297044867/1000000000 : ℝ)|^133 ≤ (20220662267271/100000000000000 : ℝ)^101
        have hw : |(297044867/1000000000 : ℝ)|=(297044867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3858933763/5000000000 : ℝ)|^133 ≤ (71097266942401/100000000000000 : ℝ)^101
        have hw : |(3858933763/5000000000 : ℝ)|=(3858933763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1563119377/10000000000 : ℝ)|^133 ≤ (4341035389401/50000000000000 : ℝ)^101
        have hw : |(-1563119377/10000000000 : ℝ)|=(1563119377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3237557757/10000000000 : ℝ)*x 0 + (1187228081/2500000000 : ℝ)*x 1 + (497174341/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3237557757/10000000000 : ℝ)^133 ≤ (11324236301951/50000000000000 : ℝ)^101 := by
    have hnat : (3237557757 : ℕ)^133*50000000000000^101 ≤ 11324236301951^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3237557757 10000000000 11324236301951 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1187228081/2500000000 : ℝ)^133 ≤ (4688554247749/12500000000000 : ℝ)^101 := by
    have hnat : (1187228081 : ℕ)^133*12500000000000^101 ≤ 4688554247749^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187228081 2500000000 4688554247749 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497174341/1000000000 : ℝ)^133 ≤ (39843093400039/100000000000000 : ℝ)^101 := by
    have hnat : (497174341 : ℕ)^133*100000000000000^101 ≤ 39843093400039^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497174341 1000000000 39843093400039 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3237557757/10000000000 : ℝ), (1187228081/2500000000 : ℝ), (497174341/1000000000 : ℝ)] ![(11324236301951/50000000000000 : ℝ), (4688554247749/12500000000000 : ℝ), (39843093400039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3237557757/10000000000 : ℝ)|^133 ≤ (11324236301951/50000000000000 : ℝ)^101
        have hw : |(3237557757/10000000000 : ℝ)|=(3237557757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1187228081/2500000000 : ℝ)|^133 ≤ (4688554247749/12500000000000 : ℝ)^101
        have hw : |(1187228081/2500000000 : ℝ)|=(1187228081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497174341/1000000000 : ℝ)|^133 ≤ (39843093400039/100000000000000 : ℝ)^101
        have hw : |(497174341/1000000000 : ℝ)|=(497174341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-251586657/2500000000 : ℝ)*x 0 + (685347831/2000000000 : ℝ)*x 1 + (7687671411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251586657/2500000000 : ℝ)^133 ≤ (607710095337/12500000000000 : ℝ)^101 := by
    have hnat : (251586657 : ℕ)^133*12500000000000^101 ≤ 607710095337^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251586657 2500000000 607710095337 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685347831/2000000000 : ℝ)^133 ≤ (244071250481/1000000000000 : ℝ)^101 := by
    have hnat : (685347831 : ℕ)^133*1000000000000^101 ≤ 244071250481^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685347831 2000000000 244071250481 1000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7687671411/10000000000 : ℝ)^133 ≤ (1105174908959/1562500000000 : ℝ)^101 := by
    have hnat : (7687671411 : ℕ)^133*1562500000000^101 ≤ 1105174908959^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7687671411 10000000000 1105174908959 1562500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-251586657/2500000000 : ℝ), (685347831/2000000000 : ℝ), (7687671411/10000000000 : ℝ)] ![(607710095337/12500000000000 : ℝ), (244071250481/1000000000000 : ℝ), (1105174908959/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-251586657/2500000000 : ℝ)|^133 ≤ (607710095337/12500000000000 : ℝ)^101
        have hw : |(-251586657/2500000000 : ℝ)|=(251586657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685347831/2000000000 : ℝ)|^133 ≤ (244071250481/1000000000000 : ℝ)^101
        have hw : |(685347831/2000000000 : ℝ)|=(685347831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7687671411/10000000000 : ℝ)|^133 ≤ (1105174908959/1562500000000 : ℝ)^101
        have hw : |(7687671411/10000000000 : ℝ)|=(7687671411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2141264769/2500000000 : ℝ)*x 0 + (-164113/8000000 : ℝ)*x 1 + (675587197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141264769/2500000000 : ℝ)^133 ≤ (81548731588019/100000000000000 : ℝ)^101 := by
    have hnat : (2141264769 : ℕ)^133*100000000000000^101 ≤ 81548731588019^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141264769 2500000000 81548731588019 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164113/8000000 : ℝ)^133 ≤ (598767069839/100000000000000 : ℝ)^101 := by
    have hnat : (164113 : ℕ)^133*100000000000000^101 ≤ 598767069839^101*8000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164113 8000000 598767069839 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675587197/2500000000 : ℝ)^133 ≤ (8926250661943/50000000000000 : ℝ)^101 := by
    have hnat : (675587197 : ℕ)^133*50000000000000^101 ≤ 8926250661943^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675587197 2500000000 8926250661943 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141264769/2500000000 : ℝ), (-164113/8000000 : ℝ), (675587197/2500000000 : ℝ)] ![(81548731588019/100000000000000 : ℝ), (598767069839/100000000000000 : ℝ), (8926250661943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141264769/2500000000 : ℝ)|^133 ≤ (81548731588019/100000000000000 : ℝ)^101
        have hw : |(2141264769/2500000000 : ℝ)|=(2141264769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-164113/8000000 : ℝ)|^133 ≤ (598767069839/100000000000000 : ℝ)^101
        have hw : |(-164113/8000000 : ℝ)|=(164113/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675587197/2500000000 : ℝ)|^133 ≤ (8926250661943/50000000000000 : ℝ)^101
        have hw : |(675587197/2500000000 : ℝ)|=(675587197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4041509863/10000000000 : ℝ)*x 0 + (876002421/1250000000 : ℝ)*x 1 + (-1335164401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4041509863/10000000000 : ℝ)^133 ≤ (15165411796483/50000000000000 : ℝ)^101 := by
    have hnat : (4041509863 : ℕ)^133*50000000000000^101 ≤ 15165411796483^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041509863 10000000000 15165411796483 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876002421/1250000000 : ℝ)^133 ≤ (626145105843/1000000000000 : ℝ)^101 := by
    have hnat : (876002421 : ℕ)^133*1000000000000^101 ≤ 626145105843^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876002421 1250000000 626145105843 1000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1335164401/10000000000 : ℝ)^133 ≤ (7054665812939/100000000000000 : ℝ)^101 := by
    have hnat : (1335164401 : ℕ)^133*100000000000000^101 ≤ 7054665812939^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335164401 10000000000 7054665812939 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4041509863/10000000000 : ℝ), (876002421/1250000000 : ℝ), (-1335164401/10000000000 : ℝ)] ![(15165411796483/50000000000000 : ℝ), (626145105843/1000000000000 : ℝ), (7054665812939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4041509863/10000000000 : ℝ)|^133 ≤ (15165411796483/50000000000000 : ℝ)^101
        have hw : |(4041509863/10000000000 : ℝ)|=(4041509863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876002421/1250000000 : ℝ)|^133 ≤ (626145105843/1000000000000 : ℝ)^101
        have hw : |(876002421/1250000000 : ℝ)|=(876002421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1335164401/10000000000 : ℝ)|^133 ≤ (7054665812939/100000000000000 : ℝ)^101
        have hw : |(-1335164401/10000000000 : ℝ)|=(1335164401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1326676503/5000000000 : ℝ)*x 0 + (1795421961/5000000000 : ℝ)*x 1 + (324597033/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326676503/5000000000 : ℝ)^133 ≤ (1742749807599/10000000000000 : ℝ)^101 := by
    have hnat : (1326676503 : ℕ)^133*10000000000000^101 ≤ 1742749807599^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326676503 5000000000 1742749807599 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1795421961/5000000000 : ℝ)^133 ≤ (3244731083417/12500000000000 : ℝ)^101 := by
    have hnat : (1795421961 : ℕ)^133*12500000000000^101 ≤ 3244731083417^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795421961 5000000000 3244731083417 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324597033/500000000 : ℝ)^133 ≤ (56614653240639/100000000000000 : ℝ)^101 := by
    have hnat : (324597033 : ℕ)^133*100000000000000^101 ≤ 56614653240639^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324597033 500000000 56614653240639 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326676503/5000000000 : ℝ), (1795421961/5000000000 : ℝ), (324597033/500000000 : ℝ)] ![(1742749807599/10000000000000 : ℝ), (3244731083417/12500000000000 : ℝ), (56614653240639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326676503/5000000000 : ℝ)|^133 ≤ (1742749807599/10000000000000 : ℝ)^101
        have hw : |(1326676503/5000000000 : ℝ)|=(1326676503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1795421961/5000000000 : ℝ)|^133 ≤ (3244731083417/12500000000000 : ℝ)^101
        have hw : |(1795421961/5000000000 : ℝ)|=(1795421961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324597033/500000000 : ℝ)|^133 ≤ (56614653240639/100000000000000 : ℝ)^101
        have hw : |(324597033/500000000 : ℝ)|=(324597033/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-387802421/2500000000 : ℝ)*x 0 + (5841839681/10000000000 : ℝ)*x 1 + (648427813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387802421/2500000000 : ℝ)^133 ≤ (8595067306467/100000000000000 : ℝ)^101 := by
    have hnat : (387802421 : ℕ)^133*100000000000000^101 ≤ 8595067306467^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387802421 2500000000 8595067306467 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5841839681/10000000000 : ℝ)^133 ≤ (9854058988681/20000000000000 : ℝ)^101 := by
    have hnat : (5841839681 : ℕ)^133*20000000000000^101 ≤ 9854058988681^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5841839681 10000000000 9854058988681 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648427813/1250000000 : ℝ)^133 ≤ (21067318866951/50000000000000 : ℝ)^101 := by
    have hnat : (648427813 : ℕ)^133*50000000000000^101 ≤ 21067318866951^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648427813 1250000000 21067318866951 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-387802421/2500000000 : ℝ), (5841839681/10000000000 : ℝ), (648427813/1250000000 : ℝ)] ![(8595067306467/100000000000000 : ℝ), (9854058988681/20000000000000 : ℝ), (21067318866951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-387802421/2500000000 : ℝ)|^133 ≤ (8595067306467/100000000000000 : ℝ)^101
        have hw : |(-387802421/2500000000 : ℝ)|=(387802421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5841839681/10000000000 : ℝ)|^133 ≤ (9854058988681/20000000000000 : ℝ)^101
        have hw : |(5841839681/10000000000 : ℝ)|=(5841839681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648427813/1250000000 : ℝ)|^133 ≤ (21067318866951/50000000000000 : ℝ)^101
        have hw : |(648427813/1250000000 : ℝ)|=(648427813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (961145021/1250000000 : ℝ)*x 0 + (573859/400000000 : ℝ)*x 1 + (982476441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (961145021/1250000000 : ℝ)^133 ≤ (70749231974087/100000000000000 : ℝ)^101 := by
    have hnat : (961145021 : ℕ)^133*100000000000000^101 ≤ 70749231974087^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961145021 1250000000 70749231974087 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (573859/400000000 : ℝ)^133 ≤ (9013262263/50000000000000 : ℝ)^101 := by
    have hnat : (573859 : ℕ)^133*50000000000000^101 ≤ 9013262263^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573859 400000000 9013262263 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982476441/2500000000 : ℝ)^133 ≤ (14616370744621/50000000000000 : ℝ)^101 := by
    have hnat : (982476441 : ℕ)^133*50000000000000^101 ≤ 14616370744621^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982476441 2500000000 14616370744621 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(961145021/1250000000 : ℝ), (573859/400000000 : ℝ), (982476441/2500000000 : ℝ)] ![(70749231974087/100000000000000 : ℝ), (9013262263/50000000000000 : ℝ), (14616370744621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(961145021/1250000000 : ℝ)|^133 ≤ (70749231974087/100000000000000 : ℝ)^101
        have hw : |(961145021/1250000000 : ℝ)|=(961145021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(573859/400000000 : ℝ)|^133 ≤ (9013262263/50000000000000 : ℝ)^101
        have hw : |(573859/400000000 : ℝ)|=(573859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(982476441/2500000000 : ℝ)|^133 ≤ (14616370744621/50000000000000 : ℝ)^101
        have hw : |(982476441/2500000000 : ℝ)|=(982476441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3634346437/10000000000 : ℝ)*x 0 + (6848031669/10000000000 : ℝ)*x 1 + (-263749751/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3634346437/10000000000 : ℝ)^133 ≤ (131863761363/500000000000 : ℝ)^101 := by
    have hnat : (3634346437 : ℕ)^133*500000000000^101 ≤ 131863761363^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3634346437 10000000000 131863761363 500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6848031669/10000000000 : ℝ)^133 ≤ (60739020365619/100000000000000 : ℝ)^101 := by
    have hnat : (6848031669 : ℕ)^133*100000000000000^101 ≤ 60739020365619^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6848031669 10000000000 60739020365619 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263749751/1250000000 : ℝ)^133 ≤ (12888227345943/100000000000000 : ℝ)^101 := by
    have hnat : (263749751 : ℕ)^133*100000000000000^101 ≤ 12888227345943^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263749751 1250000000 12888227345943 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3634346437/10000000000 : ℝ), (6848031669/10000000000 : ℝ), (-263749751/1250000000 : ℝ)] ![(131863761363/500000000000 : ℝ), (60739020365619/100000000000000 : ℝ), (12888227345943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3634346437/10000000000 : ℝ)|^133 ≤ (131863761363/500000000000 : ℝ)^101
        have hw : |(3634346437/10000000000 : ℝ)|=(3634346437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6848031669/10000000000 : ℝ)|^133 ≤ (60739020365619/100000000000000 : ℝ)^101
        have hw : |(6848031669/10000000000 : ℝ)|=(6848031669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263749751/1250000000 : ℝ)|^133 ≤ (12888227345943/100000000000000 : ℝ)^101
        have hw : |(-263749751/1250000000 : ℝ)|=(263749751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304083_s2_s2_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (415443779/1000000000 : ℝ)*x 0 + (569935493/1250000000 : ℝ)*x 1 + (4308585307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415443779/1000000000 : ℝ)^133 ≤ (3145175306989/10000000000000 : ℝ)^101 := by
    have hnat : (415443779 : ℕ)^133*10000000000000^101 ≤ 3145175306989^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415443779 1000000000 3145175306989 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569935493/1250000000 : ℝ)^133 ≤ (8887699933981/25000000000000 : ℝ)^101 := by
    have hnat : (569935493 : ℕ)^133*25000000000000^101 ≤ 8887699933981^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569935493 1250000000 8887699933981 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4308585307/10000000000 : ℝ)^133 ≤ (32997447182827/100000000000000 : ℝ)^101 := by
    have hnat : (4308585307 : ℕ)^133*100000000000000^101 ≤ 32997447182827^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308585307 10000000000 32997447182827 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(415443779/1000000000 : ℝ), (569935493/1250000000 : ℝ), (4308585307/10000000000 : ℝ)] ![(3145175306989/10000000000000 : ℝ), (8887699933981/25000000000000 : ℝ), (32997447182827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(415443779/1000000000 : ℝ)|^133 ≤ (3145175306989/10000000000000 : ℝ)^101
        have hw : |(415443779/1000000000 : ℝ)|=(415443779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569935493/1250000000 : ℝ)|^133 ≤ (8887699933981/25000000000000 : ℝ)^101
        have hw : |(569935493/1250000000 : ℝ)|=(569935493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4308585307/10000000000 : ℝ)|^133 ≤ (32997447182827/100000000000000 : ℝ)^101
        have hw : |(4308585307/10000000000 : ℝ)|=(4308585307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304083_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((13919/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13919/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((73739/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(73739/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39733/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39733/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((47801/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47801/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5631/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5631/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10493/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10493/20000 : ℝ)*X 1 2) := by
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
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (13919/20000 : ℝ) ^ (33/8 : ℝ) ≤ (2802492277919679617/12500000000000000000 : ℝ) := by
    have hpowers : (13919/20000 : ℝ)^33 ≤ (2802492277919679617/12500000000000000000 : ℝ)^8 := by
      have hnat : (13919 : ℕ)^33*12500000000000000000^8 ≤ 2802492277919679617^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13919 20000 2802492277919679617 12500000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13919/20000 : ℝ)) (X := (2802492277919679617/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (15302492277919679617/12500000000000000000 : ℝ) ≤ (5251308065337709/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (15302492277919679617/12500000000000000000 : ℝ)^8 ≤ (5251308065337709/5000000000000000 : ℝ)^33 := by
      have hnat : (15302492277919679617 : ℕ)^8*5000000000000000^33 ≤ 5251308065337709^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15302492277919679617 12500000000000000000 5251308065337709 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5251308065337709/5000000000000000 : ℝ)) (X := (15302492277919679617/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (9052492277919679617/6250000000000000000 : ℝ) ≤ (1093964393697847/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (9052492277919679617/6250000000000000000 : ℝ)^8 ≤ (1093964393697847/1000000000000000 : ℝ)^33 := by
      have hnat : (9052492277919679617 : ℕ)^8*1000000000000000^33 ≤ 1093964393697847^33*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9052492277919679617 6250000000000000000 1093964393697847 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1093964393697847/1000000000000000 : ℝ)) (X := (9052492277919679617/6250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(251308065337709/3479750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(109256951575763/1739875000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (13919/20000 : ℝ)) (alpha := (251308065337709/3479750000000000 : ℝ)) (beta := (109256951575763/1739875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13919/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(251308065337709/3479750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(109256951575763/1739875000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (73739/100000 : ℝ) ^ (33/8 : ℝ) ≤ (28461063891184584261/100000000000000000000 : ℝ) := by
    have hpowers : (73739/100000 : ℝ)^33 ≤ (28461063891184584261/100000000000000000000 : ℝ)^8 := by
      have hnat : (73739 : ℕ)^33*100000000000000000000^8 ≤ 28461063891184584261^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73739 100000 28461063891184584261 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73739/100000 : ℝ)) (X := (28461063891184584261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (128461063891184584261/100000000000000000000 : ℝ) ≤ (531298826076359/500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (128461063891184584261/100000000000000000000 : ℝ)^8 ≤ (531298826076359/500000000000000 : ℝ)^33 := by
      have hnat : (128461063891184584261 : ℕ)^8*500000000000000^33 ≤ 531298826076359^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        128461063891184584261 100000000000000000000 531298826076359 500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (531298826076359/500000000000000 : ℝ)) (X := (128461063891184584261/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (78461063891184584261/50000000000000000000 : ℝ) ≤ (11154204206353171/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (78461063891184584261/50000000000000000000 : ℝ)^8 ≤ (11154204206353171/10000000000000000 : ℝ)^33 := by
      have hnat : (78461063891184584261 : ℕ)^8*10000000000000000^33 ≤ 11154204206353171^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78461063891184584261 50000000000000000000 11154204206353171 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11154204206353171/10000000000000000 : ℝ)) (X := (78461063891184584261/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(31298826076359/368695000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(528227684825991/7373900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (73739/100000 : ℝ)) (alpha := (31298826076359/368695000000000 : ℝ)) (beta := (528227684825991/7373900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (73739/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(31298826076359/368695000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(528227684825991/7373900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (39733/50000 : ℝ) ^ (33/8 : ℝ) ≤ (38747892020360499153/100000000000000000000 : ℝ) := by
    have hpowers : (39733/50000 : ℝ)^33 ≤ (38747892020360499153/100000000000000000000 : ℝ)^8 := by
      have hnat : (39733 : ℕ)^33*100000000000000000000^8 ≤ 38747892020360499153^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39733 50000 38747892020360499153 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39733/50000 : ℝ)) (X := (38747892020360499153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (138747892020360499153/100000000000000000000 : ℝ) ≤ (676642298517573/625000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (138747892020360499153/100000000000000000000 : ℝ)^8 ≤ (676642298517573/625000000000000 : ℝ)^33 := by
      have hnat : (138747892020360499153 : ℕ)^8*625000000000000^33 ≤ 676642298517573^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        138747892020360499153 100000000000000000000 676642298517573 625000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (676642298517573/625000000000000 : ℝ)) (X := (138747892020360499153/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (88747892020360499153/50000000000000000000 : ℝ) ≤ (5746180005504399/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (88747892020360499153/50000000000000000000 : ℝ)^8 ≤ (5746180005504399/5000000000000000 : ℝ)^33 := by
      have hnat : (88747892020360499153 : ℕ)^8*5000000000000000^33 ≤ 5746180005504399^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88747892020360499153 50000000000000000000 5746180005504399 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5746180005504399/5000000000000000 : ℝ)) (X := (88747892020360499153/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(51642298517573/496662500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(66608323472763/794660000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (39733/50000 : ℝ)) (alpha := (51642298517573/496662500000000 : ℝ)) (beta := (66608323472763/794660000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (39733/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(51642298517573/496662500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(66608323472763/794660000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_2 : ((3713667873/10000000000 : ℝ)*X 2 0+(82445863/125000000 : ℝ)*X 2 1+(-1187309233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((643083173/2000000000 : ℝ)*X 0 0+(4711687653/10000000000 : ℝ)*X 0 1+(5027593647/10000000000 : ℝ)*X 0 2+(643083173/2000000000 : ℝ)*X 1 0+(4711687653/10000000000 : ℝ)*X 1 1+(5027593647/10000000000 : ℝ)*X 1 2+(643083173/2000000000 : ℝ)*X 2 0+(4711687653/10000000000 : ℝ)*X 2 1+(5027593647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1081560139/5000000000 : ℝ)*X 0 0+(5001699777/10000000000 : ℝ)*X 0 1+(5592799759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((25504981/40000000 : ℝ)*X 1 0+(1894841/1000000000 : ℝ)*X 1 1+(2712048479/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((297044867/1000000000 : ℝ)*X 2 0+(3858933763/5000000000 : ℝ)*X 2 1+(-1563119377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((3237557757/10000000000 : ℝ)*X 0 0+(1187228081/2500000000 : ℝ)*X 0 1+(497174341/1000000000 : ℝ)*X 0 2+(3237557757/10000000000 : ℝ)*X 1 0+(1187228081/2500000000 : ℝ)*X 1 1+(497174341/1000000000 : ℝ)*X 1 2+(3237557757/10000000000 : ℝ)*X 2 0+(1187228081/2500000000 : ℝ)*X 2 1+(497174341/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-251586657/2500000000 : ℝ)*X 0 0+(685347831/2000000000 : ℝ)*X 0 1+(7687671411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2141264769/2500000000 : ℝ)*X 1 0+(-164113/8000000 : ℝ)*X 1 1+(675587197/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((4041509863/10000000000 : ℝ)*X 2 0+(876002421/1250000000 : ℝ)*X 2 1+(-1335164401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1326676503/5000000000 : ℝ)*X 0 0+(1795421961/5000000000 : ℝ)*X 0 1+(324597033/500000000 : ℝ)*X 0 2+(1326676503/5000000000 : ℝ)*X 1 0+(1795421961/5000000000 : ℝ)*X 1 1+(324597033/500000000 : ℝ)*X 1 2+(1326676503/5000000000 : ℝ)*X 2 0+(1795421961/5000000000 : ℝ)*X 2 1+(324597033/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-387802421/2500000000 : ℝ)*X 0 0+(5841839681/10000000000 : ℝ)*X 0 1+(648427813/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((961145021/1250000000 : ℝ)*X 1 0+(573859/400000000 : ℝ)*X 1 1+(982476441/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((3634346437/10000000000 : ℝ)*X 2 0+(6848031669/10000000000 : ℝ)*X 2 1+(-263749751/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((415443779/1000000000 : ℝ)*X 0 0+(569935493/1250000000 : ℝ)*X 0 1+(4308585307/10000000000 : ℝ)*X 0 2+(415443779/1000000000 : ℝ)*X 1 0+(569935493/1250000000 : ℝ)*X 1 1+(4308585307/10000000000 : ℝ)*X 1 2+(415443779/1000000000 : ℝ)*X 2 0+(569935493/1250000000 : ℝ)*X 2 1+(4308585307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304083_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((47801/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47801/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (62422083874071235640800140309/4078088401135300000000000000000000 : ℝ) := by norm_num
    linear_combination (89936980743/500000000000 : ℝ)*(base7) + (80989066141/125000000000 : ℝ)*(base49) + (16741063329/50000000000 : ℝ)*(base60) + (3633824322227/1000000000000 : ℝ)*(major_s2_0) + (3633824322227/1000000000000 : ℝ)*(major_s2_1) + (3633824322227/1000000000000 : ℝ)*(major_s2_2) + (191341513/250000000000 : ℝ)*(sp_s2_6) + (4759071710707/1000000000000 : ℝ)*(sp_s2_7) + (1189796067767/250000000000 : ℝ)*(sp_s2_8) + (951837195211/200000000000 : ℝ)*(sp_s2_9) + (102998098821/40000000000 : ℝ)*(sp_s2_13) + (4820889/250000000000 : ℝ)*(sp_s2_14) + (94981791/1000000000000 : ℝ)*(sp_s2_21) + (1704987/1000000000000 : ℝ)*(sp_s2_22) + (239584387509/100000000000 : ℝ)*(f.failure) + (951837195211/200000000000 : ℝ)*(f.sum) + (209855737238192561381/292987168700000000000000000000000 : ℝ)*base63 + (52790842695487/158932000000000000000000000 : ℝ)*base64 + (114962218407293/737390000000000000000000000 : ℝ)*base67 + (484352605904681/1986650000000000000000000000 : ℝ)*base68 + (107448921393558540937/276521813500000000000000000000000 : ℝ)*base70 + (364101306791737/869937500000000000000000000 : ℝ)*base72 + (1119154220003593/7373900000000000000000000000 : ℝ)*base75 + (1967363835770407/3479750000000000000000000000 : ℝ)*base76 + (3221099030437087047/256593285250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (619/1250000000000000 : ℝ)*base86 + (619/1250000000000000 : ℝ)*base88 + (619/1250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((5631/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5631/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (342758231411296282507494783/27652181350000000000000000000000 : ℝ) := by norm_num
    linear_combination (3225593/500000000000 : ℝ)*(base21) + (11782307/1000000000000 : ℝ)*(base33) + (364453574417/500000000000 : ℝ)*(base40) + (283012816641/500000000000 : ℝ)*(base49) + (293281983009/500000000000 : ℝ)*(base60) + (2675175227593/1000000000000 : ℝ)*(major_s2_0) + (2675187009901/1000000000000 : ℝ)*(major_s2_1) + (2675187009901/1000000000000 : ℝ)*(major_s2_2) + (24757/1953125000 : ℝ)*(sp_s2_2) + (1793286172349/500000000000 : ℝ)*(sp_s2_14) + (3586486108307/1000000000000 : ℝ)*(sp_s2_15) + (1793270717811/500000000000 : ℝ)*(sp_s2_16) + (881898771659/500000000000 : ℝ)*(sp_s2_20) + (18613521/250000000000 : ℝ)*(sp_s2_22) + (881898771659/500000000000 : ℝ)*(f.failure) + (1793286172349/500000000000 : ℝ)*(f.sum) + (42567296542466071193/292987168700000000000000000000000 : ℝ)*base63 + (165738035405413/794660000000000000000000000 : ℝ)*base64 + (40740352396189/184347500000000000000000000 : ℝ)*base67 + (84356225332247/496662500000000000000000000 : ℝ)*base68 + (106097367864374544033/276521813500000000000000000000000 : ℝ)*base70 + (424483972599891/1739875000000000000000000000 : ℝ)*base72 + (9849378101744031/7373900000000000000000000000 : ℝ)*base74 + (1060949962605263/3479750000000000000000000000 : ℝ)*base76 + (26399280159334457199/128296642625000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (7981/6250000000000000 : ℝ)*base87 + (1731/6250000000000000 : ℝ)*base89 + (1731/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10493/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10493/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15831745093820096621300894299191/1274402625354781250000000000000000000 : ℝ) := by norm_num
    linear_combination (1216649/250000000000 : ℝ)*(base11) + (729559451939/1000000000000 : ℝ)*(base40) + (83268734283/100000000000 : ℝ)*(base49) + (4269263/1000000000000 : ℝ)*(base50) + (4980000219649/1000000000000 : ℝ)*(major_s2_0) + (4980000219649/1000000000000 : ℝ)*(major_s2_1) + (4980000219649/1000000000000 : ℝ)*(major_s2_2) + (451741/100000000000 : ℝ)*(sp_s2_9) + (50457701/1000000000000 : ℝ)*(sp_s2_15) + (20599053/500000000000 : ℝ)*(sp_s2_16) + (6676590263661/1000000000000 : ℝ)*(sp_s2_21) + (1669136168139/250000000000 : ℝ)*(sp_s2_22) + (6676549414741/1000000000000 : ℝ)*(sp_s2_23) + (3283401168079/1000000000000 : ℝ)*(sp_s2_27) + (3283401168079/1000000000000 : ℝ)*(f.failure) + (6676595130257/1000000000000 : ℝ)*(f.sum) + (75049296085278938543/292987168700000000000000000000000 : ℝ)*base62 + (76118867982613/158932000000000000000000000 : ℝ)*base65 + (105662436356401/737390000000000000000000000 : ℝ)*base66 + (434144897278999/993325000000000000000000000 : ℝ)*base69 + (10099917709362974931/276521813500000000000000000000000 : ℝ)*base71 + (865097580744999/3479750000000000000000000000 : ℝ)*base73 + (207154008570109/7373900000000000000000000000 : ℝ)*base74 + (748753596932233/1739875000000000000000000000 : ℝ)*base77 + (92503110106850786889/256593285250000000000000000000000 : ℝ)*base78 + (2739/12500000000000000 : ℝ)*base86 + (2739/12500000000000000 : ℝ)*base88 + (2739/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((13919/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13919/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((73739/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(73739/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39733/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39733/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((47801/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47801/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5631/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5631/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10493/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10493/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304083_s2 p hpa hpb X hX hprev1

#print axioms solution

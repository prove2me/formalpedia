-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301061_s7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:38:28.920016+00:00
-- url     : https://prove2.me/submissions/ce693697-0afe-4d22-9b14-6af4e6b43bcd

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
theorem collision_support_c301061_s7_s7_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1110945611/5000000000 : ℝ)*x 0 + (2309051317/5000000000 : ℝ)*x 1 + (597664913/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1110945611/5000000000 : ℝ)^65 ≤ (6797947265133/50000000000000 : ℝ)^49 := by
    have hnat : (1110945611 : ℕ)^65*50000000000000^49 ≤ 6797947265133^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110945611 5000000000 6797947265133 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2309051317/5000000000 : ℝ)^65 ≤ (7176797027109/20000000000000 : ℝ)^49 := by
    have hnat : (2309051317 : ℕ)^65*20000000000000^49 ≤ 7176797027109^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309051317 5000000000 7176797027109 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597664913/1000000000 : ℝ)^65 ≤ (10104024064317/20000000000000 : ℝ)^49 := by
    have hnat : (597664913 : ℕ)^65*20000000000000^49 ≤ 10104024064317^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597664913 1000000000 10104024064317 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1110945611/5000000000 : ℝ), (2309051317/5000000000 : ℝ), (597664913/1000000000 : ℝ)] ![(6797947265133/50000000000000 : ℝ), (7176797027109/20000000000000 : ℝ), (10104024064317/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1110945611/5000000000 : ℝ)|^65 ≤ (6797947265133/50000000000000 : ℝ)^49
        have hw : |(-1110945611/5000000000 : ℝ)|=(1110945611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2309051317/5000000000 : ℝ)|^65 ≤ (7176797027109/20000000000000 : ℝ)^49
        have hw : |(2309051317/5000000000 : ℝ)|=(2309051317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(597664913/1000000000 : ℝ)|^65 ≤ (10104024064317/20000000000000 : ℝ)^49
        have hw : |(597664913/1000000000 : ℝ)|=(597664913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4767598383/10000000000 : ℝ)*x 0 + (-145877239/625000000 : ℝ)*x 1 + (1151062503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4767598383/10000000000 : ℝ)^65 ≤ (18716500940139/50000000000000 : ℝ)^49 := by
    have hnat : (4767598383 : ℕ)^65*50000000000000^49 ≤ 18716500940139^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4767598383 10000000000 18716500940139 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145877239/625000000 : ℝ)^65 ≤ (14513604303289/100000000000000 : ℝ)^49 := by
    have hnat : (145877239 : ℕ)^65*100000000000000^49 ≤ 14513604303289^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145877239 625000000 14513604303289 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1151062503/2000000000 : ℝ)^65 ≤ (24026696905381/50000000000000 : ℝ)^49 := by
    have hnat : (1151062503 : ℕ)^65*50000000000000^49 ≤ 24026696905381^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151062503 2000000000 24026696905381 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4767598383/10000000000 : ℝ), (-145877239/625000000 : ℝ), (1151062503/2000000000 : ℝ)] ![(18716500940139/50000000000000 : ℝ), (14513604303289/100000000000000 : ℝ), (24026696905381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4767598383/10000000000 : ℝ)|^65 ≤ (18716500940139/50000000000000 : ℝ)^49
        have hw : |(4767598383/10000000000 : ℝ)|=(4767598383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-145877239/625000000 : ℝ)|^65 ≤ (14513604303289/100000000000000 : ℝ)^49
        have hw : |(-145877239/625000000 : ℝ)|=(145877239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1151062503/2000000000 : ℝ)|^65 ≤ (24026696905381/50000000000000 : ℝ)^49
        have hw : |(1151062503/2000000000 : ℝ)|=(1151062503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2433401219/5000000000 : ℝ)*x 0 + (3184758419/5000000000 : ℝ)*x 1 + (-320614059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2433401219/5000000000 : ℝ)^65 ≤ (9617434230129/25000000000000 : ℝ)^49 := by
    have hnat : (2433401219 : ℕ)^65*25000000000000^49 ≤ 9617434230129^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2433401219 5000000000 9617434230129 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3184758419/5000000000 : ℝ)^65 ≤ (10994393024247/20000000000000 : ℝ)^49 := by
    have hnat : (3184758419 : ℕ)^65*20000000000000^49 ≤ 10994393024247^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184758419 5000000000 10994393024247 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320614059/2500000000 : ℝ)^65 ≤ (163957448531/2500000000000 : ℝ)^49 := by
    have hnat : (320614059 : ℕ)^65*2500000000000^49 ≤ 163957448531^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320614059 2500000000 163957448531 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2433401219/5000000000 : ℝ), (3184758419/5000000000 : ℝ), (-320614059/2500000000 : ℝ)] ![(9617434230129/25000000000000 : ℝ), (10994393024247/20000000000000 : ℝ), (163957448531/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2433401219/5000000000 : ℝ)|^65 ≤ (9617434230129/25000000000000 : ℝ)^49
        have hw : |(2433401219/5000000000 : ℝ)|=(2433401219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3184758419/5000000000 : ℝ)|^65 ≤ (10994393024247/20000000000000 : ℝ)^49
        have hw : |(3184758419/5000000000 : ℝ)|=(3184758419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-320614059/2500000000 : ℝ)|^65 ≤ (163957448531/2500000000000 : ℝ)^49
        have hw : |(-320614059/2500000000 : ℝ)|=(320614059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6046860613/10000000000 : ℝ)*x 0 + (3137718599/10000000000 : ℝ)*x 1 + (468458481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6046860613/10000000000 : ℝ)^65 ≤ (25654455734153/50000000000000 : ℝ)^49 := by
    have hnat : (6046860613 : ℕ)^65*50000000000000^49 ≤ 25654455734153^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6046860613 10000000000 25654455734153 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3137718599/10000000000 : ℝ)^65 ≤ (1343145520447/6250000000000 : ℝ)^49 := by
    have hnat : (3137718599 : ℕ)^65*6250000000000^49 ≤ 1343145520447^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137718599 10000000000 1343145520447 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468458481/1250000000 : ℝ)^65 ≤ (27200760185491/100000000000000 : ℝ)^49 := by
    have hnat : (468458481 : ℕ)^65*100000000000000^49 ≤ 27200760185491^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468458481 1250000000 27200760185491 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6046860613/10000000000 : ℝ), (3137718599/10000000000 : ℝ), (468458481/1250000000 : ℝ)] ![(25654455734153/50000000000000 : ℝ), (1343145520447/6250000000000 : ℝ), (27200760185491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6046860613/10000000000 : ℝ)|^65 ≤ (25654455734153/50000000000000 : ℝ)^49
        have hw : |(6046860613/10000000000 : ℝ)|=(6046860613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3137718599/10000000000 : ℝ)|^65 ≤ (1343145520447/6250000000000 : ℝ)^49
        have hw : |(3137718599/10000000000 : ℝ)|=(3137718599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(468458481/1250000000 : ℝ)|^65 ≤ (27200760185491/100000000000000 : ℝ)^49
        have hw : |(468458481/1250000000 : ℝ)|=(468458481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122220063/10000000000 : ℝ)*x 0 + (233620429/625000000 : ℝ)*x 1 + (851561849/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122220063/10000000000 : ℝ)^65 ≤ (3198209337883/25000000000000 : ℝ)^49 := by
    have hnat : (2122220063 : ℕ)^65*25000000000000^49 ≤ 3198209337883^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122220063 10000000000 3198209337883 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233620429/625000000 : ℝ)^65 ≤ (27107013567129/100000000000000 : ℝ)^49 := by
    have hnat : (233620429 : ℕ)^65*100000000000000^49 ≤ 27107013567129^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233620429 625000000 27107013567129 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (851561849/1250000000 : ℝ)^65 ≤ (30050074537319/50000000000000 : ℝ)^49 := by
    have hnat : (851561849 : ℕ)^65*50000000000000^49 ≤ 30050074537319^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851561849 1250000000 30050074537319 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122220063/10000000000 : ℝ), (233620429/625000000 : ℝ), (851561849/1250000000 : ℝ)] ![(3198209337883/25000000000000 : ℝ), (27107013567129/100000000000000 : ℝ), (30050074537319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122220063/10000000000 : ℝ)|^65 ≤ (3198209337883/25000000000000 : ℝ)^49
        have hw : |(-2122220063/10000000000 : ℝ)|=(2122220063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(233620429/625000000 : ℝ)|^65 ≤ (27107013567129/100000000000000 : ℝ)^49
        have hw : |(233620429/625000000 : ℝ)|=(233620429/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(851561849/1250000000 : ℝ)|^65 ≤ (30050074537319/50000000000000 : ℝ)^49
        have hw : |(851561849/1250000000 : ℝ)|=(851561849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (527045699/1250000000 : ℝ)*x 0 + (-818448721/5000000000 : ℝ)*x 1 + (1345916193/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527045699/1250000000 : ℝ)^65 ≤ (1590153778429/5000000000000 : ℝ)^49 := by
    have hnat : (527045699 : ℕ)^65*5000000000000^49 ≤ 1590153778429^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527045699 1250000000 1590153778429 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (818448721/5000000000 : ℝ)^65 ≤ (9065158865031/100000000000000 : ℝ)^49 := by
    have hnat : (818448721 : ℕ)^65*100000000000000^49 ≤ 9065158865031^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818448721 5000000000 9065158865031 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1345916193/2000000000 : ℝ)^65 ≤ (59131765545939/100000000000000 : ℝ)^49 := by
    have hnat : (1345916193 : ℕ)^65*100000000000000^49 ≤ 59131765545939^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345916193 2000000000 59131765545939 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527045699/1250000000 : ℝ), (-818448721/5000000000 : ℝ), (1345916193/2000000000 : ℝ)] ![(1590153778429/5000000000000 : ℝ), (9065158865031/100000000000000 : ℝ), (59131765545939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527045699/1250000000 : ℝ)|^65 ≤ (1590153778429/5000000000000 : ℝ)^49
        have hw : |(527045699/1250000000 : ℝ)|=(527045699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-818448721/5000000000 : ℝ)|^65 ≤ (9065158865031/100000000000000 : ℝ)^49
        have hw : |(-818448721/5000000000 : ℝ)|=(818448721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1345916193/2000000000 : ℝ)|^65 ≤ (59131765545939/100000000000000 : ℝ)^49
        have hw : |(1345916193/2000000000 : ℝ)|=(1345916193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (33725957/78125000 : ℝ)*x 0 + (1822848751/2500000000 : ℝ)*x 1 + (-101113947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33725957/78125000 : ℝ)^65 ≤ (16406558105511/50000000000000 : ℝ)^49 := by
    have hnat : (33725957 : ℕ)^65*50000000000000^49 ≤ 16406558105511^49*78125000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33725957 78125000 16406558105511 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1822848751/2500000000 : ℝ)^65 ≤ (65767918371/100000000000 : ℝ)^49 := by
    have hnat : (1822848751 : ℕ)^65*100000000000^49 ≤ 65767918371^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822848751 2500000000 65767918371 100000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101113947/2500000000 : ℝ)^65 ≤ (56758616213/4000000000000 : ℝ)^49 := by
    have hnat : (101113947 : ℕ)^65*4000000000000^49 ≤ 56758616213^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101113947 2500000000 56758616213 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33725957/78125000 : ℝ), (1822848751/2500000000 : ℝ), (-101113947/2500000000 : ℝ)] ![(16406558105511/50000000000000 : ℝ), (65767918371/100000000000 : ℝ), (56758616213/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33725957/78125000 : ℝ)|^65 ≤ (16406558105511/50000000000000 : ℝ)^49
        have hw : |(33725957/78125000 : ℝ)|=(33725957/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1822848751/2500000000 : ℝ)|^65 ≤ (65767918371/100000000000 : ℝ)^49
        have hw : |(1822848751/2500000000 : ℝ)|=(1822848751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101113947/2500000000 : ℝ)|^65 ≤ (56758616213/4000000000000 : ℝ)^49
        have hw : |(-101113947/2500000000 : ℝ)|=(101113947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2896066673/5000000000 : ℝ)*x 0 + (955652433/2000000000 : ℝ)*x 1 + (2270792799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2896066673/5000000000 : ℝ)^65 ≤ (48461636825339/100000000000000 : ℝ)^49 := by
    have hnat : (2896066673 : ℕ)^65*100000000000000^49 ≤ 48461636825339^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2896066673 5000000000 48461636825339 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955652433/2000000000 : ℝ)^65 ≤ (37544109031821/100000000000000 : ℝ)^49 := by
    have hnat : (955652433 : ℕ)^65*100000000000000^49 ≤ 37544109031821^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955652433 2000000000 37544109031821 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270792799/10000000000 : ℝ)^65 ≤ (2798850824137/20000000000000 : ℝ)^49 := by
    have hnat : (2270792799 : ℕ)^65*20000000000000^49 ≤ 2798850824137^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270792799 10000000000 2798850824137 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2896066673/5000000000 : ℝ), (955652433/2000000000 : ℝ), (2270792799/10000000000 : ℝ)] ![(48461636825339/100000000000000 : ℝ), (37544109031821/100000000000000 : ℝ), (2798850824137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2896066673/5000000000 : ℝ)|^65 ≤ (48461636825339/100000000000000 : ℝ)^49
        have hw : |(2896066673/5000000000 : ℝ)|=(2896066673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(955652433/2000000000 : ℝ)|^65 ≤ (37544109031821/100000000000000 : ℝ)^49
        have hw : |(955652433/2000000000 : ℝ)|=(955652433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2270792799/10000000000 : ℝ)|^65 ≤ (2798850824137/20000000000000 : ℝ)^49
        have hw : |(2270792799/10000000000 : ℝ)|=(2270792799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-8402411/78125000 : ℝ)*x 0 + (903945571/2000000000 : ℝ)*x 1 + (6798259713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8402411/78125000 : ℝ)^65 ≤ (5192854827199/100000000000000 : ℝ)^49 := by
    have hnat : (8402411 : ℕ)^65*100000000000000^49 ≤ 5192854827199^49*78125000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8402411 78125000 5192854827199 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903945571/2000000000 : ℝ)^65 ≤ (34873528302007/100000000000000 : ℝ)^49 := by
    have hnat : (903945571 : ℕ)^65*100000000000000^49 ≤ 34873528302007^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903945571 2000000000 34873528302007 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6798259713/10000000000 : ℝ)^65 ≤ (59933616855591/100000000000000 : ℝ)^49 := by
    have hnat : (6798259713 : ℕ)^65*100000000000000^49 ≤ 59933616855591^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6798259713 10000000000 59933616855591 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8402411/78125000 : ℝ), (903945571/2000000000 : ℝ), (6798259713/10000000000 : ℝ)] ![(5192854827199/100000000000000 : ℝ), (34873528302007/100000000000000 : ℝ), (59933616855591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8402411/78125000 : ℝ)|^65 ≤ (5192854827199/100000000000000 : ℝ)^49
        have hw : |(-8402411/78125000 : ℝ)|=(8402411/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903945571/2000000000 : ℝ)|^65 ≤ (34873528302007/100000000000000 : ℝ)^49
        have hw : |(903945571/2000000000 : ℝ)|=(903945571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6798259713/10000000000 : ℝ)|^65 ≤ (59933616855591/100000000000000 : ℝ)^49
        have hw : |(6798259713/10000000000 : ℝ)|=(6798259713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (412359061/1000000000 : ℝ)*x 0 + (-1783283561/10000000000 : ℝ)*x 1 + (6715345483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412359061/1000000000 : ℝ)^65 ≤ (30878146913843/100000000000000 : ℝ)^49 := by
    have hnat : (412359061 : ℕ)^65*100000000000000^49 ≤ 30878146913843^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412359061 1000000000 30878146913843 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1783283561/10000000000 : ℝ)^65 ≤ (2031191837039/20000000000000 : ℝ)^49 := by
    have hnat : (1783283561 : ℕ)^65*20000000000000^49 ≤ 2031191837039^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783283561 10000000000 2031191837039 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6715345483/10000000000 : ℝ)^65 ≤ (58965893886467/100000000000000 : ℝ)^49 := by
    have hnat : (6715345483 : ℕ)^65*100000000000000^49 ≤ 58965893886467^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6715345483 10000000000 58965893886467 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(412359061/1000000000 : ℝ), (-1783283561/10000000000 : ℝ), (6715345483/10000000000 : ℝ)] ![(30878146913843/100000000000000 : ℝ), (2031191837039/20000000000000 : ℝ), (58965893886467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(412359061/1000000000 : ℝ)|^65 ≤ (30878146913843/100000000000000 : ℝ)^49
        have hw : |(412359061/1000000000 : ℝ)|=(412359061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1783283561/10000000000 : ℝ)|^65 ≤ (2031191837039/20000000000000 : ℝ)^49
        have hw : |(-1783283561/10000000000 : ℝ)|=(1783283561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6715345483/10000000000 : ℝ)|^65 ≤ (58965893886467/100000000000000 : ℝ)^49
        have hw : |(6715345483/10000000000 : ℝ)|=(6715345483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (152753811/250000000 : ℝ)*x 0 + (5613754893/10000000000 : ℝ)*x 1 + (-52336493/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (152753811/250000000 : ℝ)^65 ≤ (5202253233857/10000000000000 : ℝ)^49 := by
    have hnat : (152753811 : ℕ)^65*10000000000000^49 ≤ 5202253233857^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152753811 250000000 5202253233857 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5613754893/10000000000 : ℝ)^65 ≤ (11622967667093/25000000000000 : ℝ)^49 := by
    have hnat : (5613754893 : ℕ)^65*25000000000000^49 ≤ 11622967667093^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5613754893 10000000000 11622967667093 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52336493/1250000000 : ℝ)^65 ≤ (742798487341/50000000000000 : ℝ)^49 := by
    have hnat : (52336493 : ℕ)^65*50000000000000^49 ≤ 742798487341^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52336493 1250000000 742798487341 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(152753811/250000000 : ℝ), (5613754893/10000000000 : ℝ), (-52336493/1250000000 : ℝ)] ![(5202253233857/10000000000000 : ℝ), (11622967667093/25000000000000 : ℝ), (742798487341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(152753811/250000000 : ℝ)|^65 ≤ (5202253233857/10000000000000 : ℝ)^49
        have hw : |(152753811/250000000 : ℝ)|=(152753811/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5613754893/10000000000 : ℝ)|^65 ≤ (11622967667093/25000000000000 : ℝ)^49
        have hw : |(5613754893/10000000000 : ℝ)|=(5613754893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52336493/1250000000 : ℝ)|^65 ≤ (742798487341/50000000000000 : ℝ)^49
        have hw : |(-52336493/1250000000 : ℝ)|=(52336493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1858965173/2500000000 : ℝ)*x 0 + (2776895297/10000000000 : ℝ)*x 1 + (1149337339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1858965173/2500000000 : ℝ)^65 ≤ (8437756155183/12500000000000 : ℝ)^49 := by
    have hnat : (1858965173 : ℕ)^65*12500000000000^49 ≤ 8437756155183^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858965173 2500000000 8437756155183 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2776895297/10000000000 : ℝ)^65 ≤ (9137652830841/50000000000000 : ℝ)^49 := by
    have hnat : (2776895297 : ℕ)^65*50000000000000^49 ≤ 9137652830841^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2776895297 10000000000 9137652830841 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1149337339/5000000000 : ℝ)^65 ≤ (14222645084043/100000000000000 : ℝ)^49 := by
    have hnat : (1149337339 : ℕ)^65*100000000000000^49 ≤ 14222645084043^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149337339 5000000000 14222645084043 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1858965173/2500000000 : ℝ), (2776895297/10000000000 : ℝ), (1149337339/5000000000 : ℝ)] ![(8437756155183/12500000000000 : ℝ), (9137652830841/50000000000000 : ℝ), (14222645084043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1858965173/2500000000 : ℝ)|^65 ≤ (8437756155183/12500000000000 : ℝ)^49
        have hw : |(1858965173/2500000000 : ℝ)|=(1858965173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2776895297/10000000000 : ℝ)|^65 ≤ (9137652830841/50000000000000 : ℝ)^49
        have hw : |(2776895297/10000000000 : ℝ)|=(2776895297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1149337339/5000000000 : ℝ)|^65 ≤ (14222645084043/100000000000000 : ℝ)^49
        have hw : |(1149337339/5000000000 : ℝ)|=(1149337339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1030587559/10000000000 : ℝ)*x 0 + (554945487/1000000000 : ℝ)*x 1 + (5868055797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030587559/10000000000 : ℝ)^65 ≤ (4907122527367/100000000000000 : ℝ)^49 := by
    have hnat : (1030587559 : ℕ)^65*100000000000000^49 ≤ 4907122527367^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030587559 10000000000 4907122527367 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554945487/1000000000 : ℝ)^65 ≤ (1831471719503/4000000000000 : ℝ)^49 := by
    have hnat : (554945487 : ℕ)^65*4000000000000^49 ≤ 1831471719503^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554945487 1000000000 1831471719503 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5868055797/10000000000 : ℝ)^65 ≤ (49306084476017/100000000000000 : ℝ)^49 := by
    have hnat : (5868055797 : ℕ)^65*100000000000000^49 ≤ 49306084476017^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5868055797 10000000000 49306084476017 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1030587559/10000000000 : ℝ), (554945487/1000000000 : ℝ), (5868055797/10000000000 : ℝ)] ![(4907122527367/100000000000000 : ℝ), (1831471719503/4000000000000 : ℝ), (49306084476017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1030587559/10000000000 : ℝ)|^65 ≤ (4907122527367/100000000000000 : ℝ)^49
        have hw : |(-1030587559/10000000000 : ℝ)|=(1030587559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554945487/1000000000 : ℝ)|^65 ≤ (1831471719503/4000000000000 : ℝ)^49
        have hw : |(554945487/1000000000 : ℝ)|=(554945487/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5868055797/10000000000 : ℝ)|^65 ≤ (49306084476017/100000000000000 : ℝ)^49
        have hw : |(5868055797/10000000000 : ℝ)|=(5868055797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (37840703/62500000 : ℝ)*x 0 + (-1144049699/10000000000 : ℝ)*x 1 + (1322489881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37840703/62500000 : ℝ)^65 ≤ (51395057886193/100000000000000 : ℝ)^49 := by
    have hnat : (37840703 : ℕ)^65*100000000000000^49 ≤ 51395057886193^49*62500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37840703 62500000 51395057886193 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144049699/10000000000 : ℝ)^65 ≤ (5636354820229/100000000000000 : ℝ)^49 := by
    have hnat : (1144049699 : ℕ)^65*100000000000000^49 ≤ 5636354820229^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144049699 10000000000 5636354820229 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1322489881/2500000000 : ℝ)^65 ≤ (2685536705487/6250000000000 : ℝ)^49 := by
    have hnat : (1322489881 : ℕ)^65*6250000000000^49 ≤ 2685536705487^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322489881 2500000000 2685536705487 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(37840703/62500000 : ℝ), (-1144049699/10000000000 : ℝ), (1322489881/2500000000 : ℝ)] ![(51395057886193/100000000000000 : ℝ), (5636354820229/100000000000000 : ℝ), (2685536705487/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(37840703/62500000 : ℝ)|^65 ≤ (51395057886193/100000000000000 : ℝ)^49
        have hw : |(37840703/62500000 : ℝ)|=(37840703/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1144049699/10000000000 : ℝ)|^65 ≤ (5636354820229/100000000000000 : ℝ)^49
        have hw : |(-1144049699/10000000000 : ℝ)|=(1144049699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1322489881/2500000000 : ℝ)|^65 ≤ (2685536705487/6250000000000 : ℝ)^49
        have hw : |(1322489881/2500000000 : ℝ)|=(1322489881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4079901799/10000000000 : ℝ)*x 0 + (1447687653/2000000000 : ℝ)*x 1 + (-190497777/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4079901799/10000000000 : ℝ)^65 ≤ (3805615737923/12500000000000 : ℝ)^49 := by
    have hnat : (4079901799 : ℕ)^65*12500000000000^49 ≤ 3805615737923^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4079901799 10000000000 3805615737923 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1447687653/2000000000 : ℝ)^65 ≤ (32567515919759/50000000000000 : ℝ)^49 := by
    have hnat : (1447687653 : ℕ)^65*50000000000000^49 ≤ 32567515919759^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1447687653 2000000000 32567515919759 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190497777/2000000000 : ℝ)^65 ≤ (2210021120181/50000000000000 : ℝ)^49 := by
    have hnat : (190497777 : ℕ)^65*50000000000000^49 ≤ 2210021120181^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190497777 2000000000 2210021120181 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4079901799/10000000000 : ℝ), (1447687653/2000000000 : ℝ), (-190497777/2000000000 : ℝ)] ![(3805615737923/12500000000000 : ℝ), (32567515919759/50000000000000 : ℝ), (2210021120181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4079901799/10000000000 : ℝ)|^65 ≤ (3805615737923/12500000000000 : ℝ)^49
        have hw : |(4079901799/10000000000 : ℝ)|=(4079901799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1447687653/2000000000 : ℝ)|^65 ≤ (32567515919759/50000000000000 : ℝ)^49
        have hw : |(1447687653/2000000000 : ℝ)|=(1447687653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-190497777/2000000000 : ℝ)|^65 ≤ (2210021120181/50000000000000 : ℝ)^49
        have hw : |(-190497777/2000000000 : ℝ)|=(190497777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301061_s7_s7_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7718371779/10000000000 : ℝ)*x 0 + (91974677/400000000 : ℝ)*x 1 + (1187150157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7718371779/10000000000 : ℝ)^65 ≤ (35462503703013/50000000000000 : ℝ)^49 := by
    have hnat : (7718371779 : ℕ)^65*50000000000000^49 ≤ 35462503703013^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7718371779 10000000000 35462503703013 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91974677/400000000 : ℝ)^65 ≤ (14228327101597/100000000000000 : ℝ)^49 := by
    have hnat : (91974677 : ℕ)^65*100000000000000^49 ≤ 14228327101597^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91974677 400000000 14228327101597 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1187150157/5000000000 : ℝ)^65 ≤ (14846665484447/100000000000000 : ℝ)^49 := by
    have hnat : (1187150157 : ℕ)^65*100000000000000^49 ≤ 14846665484447^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187150157 5000000000 14846665484447 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7718371779/10000000000 : ℝ), (91974677/400000000 : ℝ), (1187150157/5000000000 : ℝ)] ![(35462503703013/50000000000000 : ℝ), (14228327101597/100000000000000 : ℝ), (14846665484447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7718371779/10000000000 : ℝ)|^65 ≤ (35462503703013/50000000000000 : ℝ)^49
        have hw : |(7718371779/10000000000 : ℝ)|=(7718371779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91974677/400000000 : ℝ)|^65 ≤ (14228327101597/100000000000000 : ℝ)^49
        have hw : |(91974677/400000000 : ℝ)|=(91974677/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1187150157/5000000000 : ℝ)|^65 ≤ (14846665484447/100000000000000 : ℝ)^49
        have hw : |(1187150157/5000000000 : ℝ)|=(1187150157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301061_s7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev6 : (0 : ℝ) ≤ ((11819/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11819/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16137/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16137/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29633/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29633/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((41157/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41157/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46961/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46961/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8593/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8593/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev6 with ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩
  have s7_pow0 : (11819/20000 : ℝ) ^ (129/32 : ℝ) ≤ (2999189570219049277/25000000000000000000 : ℝ) := by
    have hpowers : (11819/20000 : ℝ)^129 ≤ (2999189570219049277/25000000000000000000 : ℝ)^32 := by
      have hnat : (11819 : ℕ)^129*25000000000000000000^32 ≤ 2999189570219049277^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11819 20000 2999189570219049277 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11819/20000 : ℝ)) (X := (2999189570219049277/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner0a : (27999189570219049277/25000000000000000000 : ℝ) ≤ (2057008088118423/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (27999189570219049277/25000000000000000000 : ℝ)^32 ≤ (2057008088118423/2000000000000000 : ℝ)^129 := by
      have hnat : (27999189570219049277 : ℕ)^32*2000000000000000^129 ≤ 2057008088118423^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27999189570219049277 25000000000000000000 2057008088118423 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2057008088118423/2000000000000000 : ℝ)) (X := (27999189570219049277/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner0b : (15499189570219049277/12500000000000000000 : ℝ) ≤ (10547966419762273/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (15499189570219049277/12500000000000000000 : ℝ)^32 ≤ (10547966419762273/10000000000000000 : ℝ)^129 := by
      have hnat : (15499189570219049277 : ℕ)^32*10000000000000000^129 ≤ 10547966419762273^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15499189570219049277 12500000000000000000 10547966419762273 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10547966419762273/10000000000000000 : ℝ)) (X := (15499189570219049277/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s7_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(57008088118423/1181900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(131462989585079/2954750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (11819/20000 : ℝ)) (alpha := (57008088118423/1181900000000000 : ℝ)) (beta := (131462989585079/2954750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow0,s7_corner0a]) (by linarith only [s7_pow0,s7_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11819/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(57008088118423/1181900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(131462989585079/2954750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow1 : (16137/25000 : ℝ) ^ (129/32 : ℝ) ≤ (428084996713293707/2500000000000000000 : ℝ) := by
    have hpowers : (16137/25000 : ℝ)^129 ≤ (428084996713293707/2500000000000000000 : ℝ)^32 := by
      have hnat : (16137 : ℕ)^129*2500000000000000000^32 ≤ 428084996713293707^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16137 25000 428084996713293707 2500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16137/25000 : ℝ)) (X := (428084996713293707/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner1a : (2928084996713293707/2500000000000000000 : ℝ) ≤ (1299983680272983/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2928084996713293707/2500000000000000000 : ℝ)^32 ≤ (1299983680272983/1250000000000000 : ℝ)^129 := by
      have hnat : (2928084996713293707 : ℕ)^32*1250000000000000^129 ≤ 1299983680272983^129*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2928084996713293707 2500000000000000000 1299983680272983 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1299983680272983/1250000000000000 : ℝ)) (X := (2928084996713293707/2500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner1b : (1678084996713293707/1250000000000000000 : ℝ) ≤ (5378957512258087/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (1678084996713293707/1250000000000000000 : ℝ)^32 ≤ (5378957512258087/5000000000000000 : ℝ)^129 := by
      have hnat : (1678084996713293707 : ℕ)^32*5000000000000000^129 ≤ 5378957512258087^129*1250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1678084996713293707 1250000000000000000 5378957512258087 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5378957512258087/5000000000000000 : ℝ)) (X := (1678084996713293707/1250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s7_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(16661226757661/268950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(35804558233231/645480000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (16137/25000 : ℝ)) (alpha := (16661226757661/268950000000000 : ℝ)) (beta := (35804558233231/645480000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow1,s7_corner1a]) (by linarith only [s7_pow1,s7_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (16137/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(16661226757661/268950000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(35804558233231/645480000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow2 : (29633/50000 : ℝ) ^ (129/32 : ℝ) ≤ (6068657764373136031/50000000000000000000 : ℝ) := by
    have hpowers : (29633/50000 : ℝ)^129 ≤ (6068657764373136031/50000000000000000000 : ℝ)^32 := by
      have hnat : (29633 : ℕ)^129*50000000000000000000^32 ≤ 6068657764373136031^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29633 50000 6068657764373136031 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29633/50000 : ℝ)) (X := (6068657764373136031/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner2a : (56068657764373136031/50000000000000000000 : ℝ) ≤ (10288240877324409/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (56068657764373136031/50000000000000000000 : ℝ)^32 ≤ (10288240877324409/10000000000000000 : ℝ)^129 := by
      have hnat : (56068657764373136031 : ℕ)^32*10000000000000000^129 ≤ 10288240877324409^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56068657764373136031 50000000000000000000 10288240877324409 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10288240877324409/10000000000000000 : ℝ)) (X := (56068657764373136031/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner2b : (31068657764373136031/25000000000000000000 : ℝ) ≤ (1055389353560599/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (31068657764373136031/25000000000000000000 : ℝ)^32 ≤ (1055389353560599/1000000000000000 : ℝ)^129 := by
      have hnat : (31068657764373136031 : ℕ)^32*1000000000000000^129 ≤ 1055389353560599^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31068657764373136031 25000000000000000000 1055389353560599 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1055389353560599/1000000000000000 : ℝ)) (X := (31068657764373136031/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s7_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(288240877324409/5926600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(265652658281581/5926600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (29633/50000 : ℝ)) (alpha := (288240877324409/5926600000000000 : ℝ)) (beta := (265652658281581/5926600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow2,s7_corner2a]) (by linarith only [s7_pow2,s7_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29633/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(288240877324409/5926600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(265652658281581/5926600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s7_0 : ((-1110945611/5000000000 : ℝ)*X 0 0+(2309051317/5000000000 : ℝ)*X 0 1+(597664913/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_1 : ((4767598383/10000000000 : ℝ)*X 1 0+(-145877239/625000000 : ℝ)*X 1 1+(1151062503/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_2 : ((2433401219/5000000000 : ℝ)*X 2 0+(3184758419/5000000000 : ℝ)*X 2 1+(-320614059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_6 : ((6046860613/10000000000 : ℝ)*X 0 0+(3137718599/10000000000 : ℝ)*X 0 1+(468458481/1250000000 : ℝ)*X 0 2+(6046860613/10000000000 : ℝ)*X 1 0+(3137718599/10000000000 : ℝ)*X 1 1+(468458481/1250000000 : ℝ)*X 1 2+(6046860613/10000000000 : ℝ)*X 2 0+(3137718599/10000000000 : ℝ)*X 2 1+(468458481/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_7 : ((-2122220063/10000000000 : ℝ)*X 0 0+(233620429/625000000 : ℝ)*X 0 1+(851561849/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_8 : ((527045699/1250000000 : ℝ)*X 1 0+(-818448721/5000000000 : ℝ)*X 1 1+(1345916193/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_9 : ((33725957/78125000 : ℝ)*X 2 0+(1822848751/2500000000 : ℝ)*X 2 1+(-101113947/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_13 : ((2896066673/5000000000 : ℝ)*X 0 0+(955652433/2000000000 : ℝ)*X 0 1+(2270792799/10000000000 : ℝ)*X 0 2+(2896066673/5000000000 : ℝ)*X 1 0+(955652433/2000000000 : ℝ)*X 1 1+(2270792799/10000000000 : ℝ)*X 1 2+(2896066673/5000000000 : ℝ)*X 2 0+(955652433/2000000000 : ℝ)*X 2 1+(2270792799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_14 : ((-8402411/78125000 : ℝ)*X 0 0+(903945571/2000000000 : ℝ)*X 0 1+(6798259713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_15 : ((412359061/1000000000 : ℝ)*X 1 0+(-1783283561/10000000000 : ℝ)*X 1 1+(6715345483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_16 : ((152753811/250000000 : ℝ)*X 2 0+(5613754893/10000000000 : ℝ)*X 2 1+(-52336493/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_20 : ((1858965173/2500000000 : ℝ)*X 0 0+(2776895297/10000000000 : ℝ)*X 0 1+(1149337339/5000000000 : ℝ)*X 0 2+(1858965173/2500000000 : ℝ)*X 1 0+(2776895297/10000000000 : ℝ)*X 1 1+(1149337339/5000000000 : ℝ)*X 1 2+(1858965173/2500000000 : ℝ)*X 2 0+(2776895297/10000000000 : ℝ)*X 2 1+(1149337339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_21 : ((-1030587559/10000000000 : ℝ)*X 0 0+(554945487/1000000000 : ℝ)*X 0 1+(5868055797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_22 : ((37840703/62500000 : ℝ)*X 1 0+(-1144049699/10000000000 : ℝ)*X 1 1+(1322489881/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_23 : ((4079901799/10000000000 : ℝ)*X 2 0+(1447687653/2000000000 : ℝ)*X 2 1+(-190497777/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_27 : ((7718371779/10000000000 : ℝ)*X 0 0+(91974677/400000000 : ℝ)*X 0 1+(1187150157/5000000000 : ℝ)*X 0 2+(7718371779/10000000000 : ℝ)*X 1 0+(91974677/400000000 : ℝ)*X 1 1+(1187150157/5000000000 : ℝ)*X 1 2+(7718371779/10000000000 : ℝ)*X 2 0+(91974677/400000000 : ℝ)*X 2 1+(1187150157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301061_s7_s7_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s7_0 : (0 : ℝ) ≤ ((41157/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41157/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6043489322436351693452608711937/470975056208250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1215103/1000000000000 : ℝ)*(base50) + (285786776037/500000000000 : ℝ)*(base59) + (454917/1000000000000 : ℝ)*(base60) + (4164078527951/1000000000000 : ℝ)*(major_s7_0) + (4164078527951/1000000000000 : ℝ)*(major_s7_1) + (4164078527951/1000000000000 : ℝ)*(major_s7_2) + (25464167/1000000000000 : ℝ)*(sp_s7_0) + (5887099/200000000000 : ℝ)*(sp_s7_6) + (5513115194737/1000000000000 : ℝ)*(sp_s7_7) + (1102508700659/200000000000 : ℝ)*(sp_s7_8) + (1102607144207/200000000000 : ℝ)*(sp_s7_9) + (2814982684209/1000000000000 : ℝ)*(sp_s7_13) + (597155609/1000000000000 : ℝ)*(sp_s7_15) + (104937869/1000000000000 : ℝ)*(sp_s7_23) + (351876514963/125000000000 : ℝ)*(f.failure) + (689142582363/125000000000 : ℝ)*(f.sum) + (562484963572115647/31879181400000000000000000000000 : ℝ)*base62 + (6734532208457709/5926600000000000000000000000 : ℝ)*base65 + (509991498809261/645480000000000000000000000 : ℝ)*base67 + (4979844792427819/5926600000000000000000000000 : ℝ)*base69 + (44576248810125298189/70046485400000000000000000000000 : ℝ)*base71 + (664702514105477/1477375000000000000000000000 : ℝ)*base73 + (4101377253811/268950000000000000000000000 : ℝ)*base75 + (637640114392423/1181900000000000000000000000 : ℝ)*base77 + (51592896277615482367/190723203000000000000000000000000 : ℝ)*base79 + (43/781250000000000 : ℝ)*base86 + (43/781250000000000 : ℝ)*base88 + (43/781250000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s7_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46961/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46961/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (698927508900206784223692454489/94195011241650000000000000000000000 : ℝ) := by norm_num
    linear_combination (192847/1000000000000 : ℝ)*(base39) + (52137/100000000000 : ℝ)*(base49) + (51851336287/250000000000 : ℝ)*(base59) + (2002390475593/500000000000 : ℝ)*(major_s7_0) + (2002390475593/500000000000 : ℝ)*(major_s7_1) + (2002390475593/500000000000 : ℝ)*(major_s7_2) + (1082331/62500000000 : ℝ)*(sp_s7_2) + (2288443/250000000000 : ℝ)*(sp_s7_6) + (5680671/200000000000 : ℝ)*(sp_s7_7) + (66277596293/12500000000 : ℝ)*(sp_s7_14) + (1060447221359/200000000000 : ℝ)*(sp_s7_15) + (10604437579/2000000000 : ℝ)*(sp_s7_16) + (1353618173511/500000000000 : ℝ)*(sp_s7_20) + (77821443/1000000000000 : ℝ)*(sp_s7_27) + (2707323322237/1000000000000 : ℝ)*(f.failure) + (1060447221359/200000000000 : ℝ)*(f.sum) + (1915399376542490119/15939590700000000000000000000000 : ℝ)*base63 + (1493253870031343/2963300000000000000000000000 : ℝ)*base64 + (25546541655187/322740000000000000000000000 : ℝ)*base67 + (444568319279773/2963300000000000000000000000 : ℝ)*base68 + (6003578076308957693/35023242700000000000000000000000 : ℝ)*base70 + (1261569754239331/2954750000000000000000000000 : ℝ)*base72 + (178320709147529/268950000000000000000000000 : ℝ)*base74 + (119493713614309/147737500000000000000000000 : ℝ)*base76 + (17451424359365519381/95361601500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (3503/25000000000000000 : ℝ)*base86 + (3503/25000000000000000 : ℝ)*base88 + (3503/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s7_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8593/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8593/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (67505043697893232096388577781/12559334832220000000000000000000000 : ℝ) := by norm_num
    linear_combination (2113351/1000000000000 : ℝ)*(base15) + (119312214953/500000000000 : ℝ)*(base40) + (23657044057/100000000000 : ℝ)*(base59) + (727943101921/200000000000 : ℝ)*(major_s7_0) + (727943101921/200000000000 : ℝ)*(major_s7_1) + (727943101921/200000000000 : ℝ)*(major_s7_2) + (657023/200000000000 : ℝ)*(sp_s7_1) + (25062501/500000000000 : ℝ)*(sp_s7_2) + (27098779/1000000000000 : ℝ)*(sp_s7_9) + (145974049/1000000000000 : ℝ)*(sp_s7_20) + (4818898475563/1000000000000 : ℝ)*(sp_s7_21) + (602361634637/125000000000 : ℝ)*(sp_s7_22) + (4818821251781/1000000000000 : ℝ)*(sp_s7_23) + (1230192388981/500000000000 : ℝ)*(sp_s7_27) + (2460530752011/1000000000000 : ℝ)*(f.failure) + (4818898475563/1000000000000 : ℝ)*(f.sum) + (417604948823105731/6375836280000000000000000000000 : ℝ)*base63 + (155140377536417/1185320000000000000000000000 : ℝ)*base64 + (9870602219207/645480000000000000000000000 : ℝ)*base67 + (799684665726397/1185320000000000000000000000 : ℝ)*base69 + (138548524455062747/14009297080000000000000000000000 : ℝ)*base71 + (53531490086477/295475000000000000000000000 : ℝ)*base73 + (13109707658533/26895000000000000000000000 : ℝ)*base75 + (224331989764503/236380000000000000000000000 : ℝ)*base77 + (8812348602916469203/38144640600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (6209/25000000000000000 : ℝ)*base86 + (6209/25000000000000000 : ℝ)*base88 + (6209/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev6 : (0 : ℝ) ≤ ((11819/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11819/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16137/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16137/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29633/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29633/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((41157/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41157/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46961/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46961/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8593/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8593/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301061_s7 p hpa hpb X hX hprev6

#print axioms solution

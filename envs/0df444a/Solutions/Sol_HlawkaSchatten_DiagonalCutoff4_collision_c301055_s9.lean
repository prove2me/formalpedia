-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301055_s9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:33:10.437293+00:00
-- url     : https://prove2.me/submissions/119b45c7-9c00-4117-a210-31347e48008c

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
theorem collision_support_c301055_s9_s9_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2731886657/10000000000 : ℝ)*x 0 + (683483919/1250000000 : ℝ)*x 1 + (4747186473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2731886657/10000000000 : ℝ)^65 ≤ (4470854110587/25000000000000 : ℝ)^49 := by
    have hnat : (2731886657 : ℕ)^65*25000000000000^49 ≤ 4470854110587^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731886657 10000000000 4470854110587 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683483919/1250000000 : ℝ)^65 ≤ (44896029321349/100000000000000 : ℝ)^49 := by
    have hnat : (683483919 : ℕ)^65*100000000000000^49 ≤ 44896029321349^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683483919 1250000000 44896029321349 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4747186473/10000000000 : ℝ)^65 ≤ (37220554224807/100000000000000 : ℝ)^49 := by
    have hnat : (4747186473 : ℕ)^65*100000000000000^49 ≤ 37220554224807^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4747186473 10000000000 37220554224807 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2731886657/10000000000 : ℝ), (683483919/1250000000 : ℝ), (4747186473/10000000000 : ℝ)] ![(4470854110587/25000000000000 : ℝ), (44896029321349/100000000000000 : ℝ), (37220554224807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2731886657/10000000000 : ℝ)|^65 ≤ (4470854110587/25000000000000 : ℝ)^49
        have hw : |(-2731886657/10000000000 : ℝ)|=(2731886657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683483919/1250000000 : ℝ)|^65 ≤ (44896029321349/100000000000000 : ℝ)^49
        have hw : |(683483919/1250000000 : ℝ)|=(683483919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4747186473/10000000000 : ℝ)|^65 ≤ (37220554224807/100000000000000 : ℝ)^49
        have hw : |(4747186473/10000000000 : ℝ)|=(4747186473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4744521771/10000000000 : ℝ)*x 0 + (-503487507/2500000000 : ℝ)*x 1 + (751009281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4744521771/10000000000 : ℝ)^65 ≤ (37192841919109/100000000000000 : ℝ)^49 := by
    have hnat : (4744521771 : ℕ)^65*100000000000000^49 ≤ 37192841919109^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4744521771 10000000000 37192841919109 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503487507/2500000000 : ℝ)^65 ≤ (11934364087969/100000000000000 : ℝ)^49 := by
    have hnat : (503487507 : ℕ)^65*100000000000000^49 ≤ 11934364087969^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503487507 2500000000 11934364087969 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (751009281/1250000000 : ℝ)^65 ≤ (1271819849627/2500000000000 : ℝ)^49 := by
    have hnat : (751009281 : ℕ)^65*2500000000000^49 ≤ 1271819849627^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751009281 1250000000 1271819849627 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4744521771/10000000000 : ℝ), (-503487507/2500000000 : ℝ), (751009281/1250000000 : ℝ)] ![(37192841919109/100000000000000 : ℝ), (11934364087969/100000000000000 : ℝ), (1271819849627/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4744521771/10000000000 : ℝ)|^65 ≤ (37192841919109/100000000000000 : ℝ)^49
        have hw : |(4744521771/10000000000 : ℝ)|=(4744521771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-503487507/2500000000 : ℝ)|^65 ≤ (11934364087969/100000000000000 : ℝ)^49
        have hw : |(-503487507/2500000000 : ℝ)|=(503487507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(751009281/1250000000 : ℝ)|^65 ≤ (1271819849627/2500000000000 : ℝ)^49
        have hw : |(751009281/1250000000 : ℝ)|=(751009281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1186726453/2500000000 : ℝ)*x 0 + (2732742327/5000000000 : ℝ)*x 1 + (-2735215571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1186726453/2500000000 : ℝ)^65 ≤ (2326102198357/6250000000000 : ℝ)^49 := by
    have hnat : (1186726453 : ℕ)^65*6250000000000^49 ≤ 2326102198357^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186726453 2500000000 2326102198357 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732742327/5000000000 : ℝ)^65 ≤ (5608754412757/12500000000000 : ℝ)^49 := by
    have hnat : (2732742327 : ℕ)^65*12500000000000^49 ≤ 5608754412757^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732742327 5000000000 5608754412757 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735215571/10000000000 : ℝ)^65 ≤ (17912329500773/100000000000000 : ℝ)^49 := by
    have hnat : (2735215571 : ℕ)^65*100000000000000^49 ≤ 17912329500773^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735215571 10000000000 17912329500773 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1186726453/2500000000 : ℝ), (2732742327/5000000000 : ℝ), (-2735215571/10000000000 : ℝ)] ![(2326102198357/6250000000000 : ℝ), (5608754412757/12500000000000 : ℝ), (17912329500773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1186726453/2500000000 : ℝ)|^65 ≤ (2326102198357/6250000000000 : ℝ)^49
        have hw : |(1186726453/2500000000 : ℝ)|=(1186726453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732742327/5000000000 : ℝ)|^65 ≤ (5608754412757/12500000000000 : ℝ)^49
        have hw : |(2732742327/5000000000 : ℝ)|=(2732742327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2735215571/10000000000 : ℝ)|^65 ≤ (17912329500773/100000000000000 : ℝ)^49
        have hw : |(-2735215571/10000000000 : ℝ)|=(2735215571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5630224327/10000000000 : ℝ)*x 0 + (2105691907/5000000000 : ℝ)*x 1 + (3146909319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5630224327/10000000000 : ℝ)^65 ≤ (46672891000681/100000000000000 : ℝ)^49 := by
    have hnat : (5630224327 : ℕ)^65*100000000000000^49 ≤ 46672891000681^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5630224327 10000000000 46672891000681 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105691907/5000000000 : ℝ)^65 ≤ (31753238934773/100000000000000 : ℝ)^49 := by
    have hnat : (2105691907 : ℕ)^65*100000000000000^49 ≤ 31753238934773^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105691907 5000000000 31753238934773 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3146909319/10000000000 : ℝ)^65 ≤ (10786935019843/50000000000000 : ℝ)^49 := by
    have hnat : (3146909319 : ℕ)^65*50000000000000^49 ≤ 10786935019843^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3146909319 10000000000 10786935019843 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5630224327/10000000000 : ℝ), (2105691907/5000000000 : ℝ), (3146909319/10000000000 : ℝ)] ![(46672891000681/100000000000000 : ℝ), (31753238934773/100000000000000 : ℝ), (10786935019843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5630224327/10000000000 : ℝ)|^65 ≤ (46672891000681/100000000000000 : ℝ)^49
        have hw : |(5630224327/10000000000 : ℝ)|=(5630224327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2105691907/5000000000 : ℝ)|^65 ≤ (31753238934773/100000000000000 : ℝ)^49
        have hw : |(2105691907/5000000000 : ℝ)|=(2105691907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3146909319/10000000000 : ℝ)|^65 ≤ (10786935019843/50000000000000 : ℝ)^49
        have hw : |(3146909319/10000000000 : ℝ)|=(3146909319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2673166789/10000000000 : ℝ)*x 0 + (1048510281/2000000000 : ℝ)*x 1 + (5027727761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673166789/10000000000 : ℝ)^65 ≤ (4343827126679/25000000000000 : ℝ)^49 := by
    have hnat : (2673166789 : ℕ)^65*25000000000000^49 ≤ 4343827126679^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673166789 10000000000 4343827126679 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048510281/2000000000 : ℝ)^65 ≤ (42458515232833/100000000000000 : ℝ)^49 := by
    have hnat : (1048510281 : ℕ)^65*100000000000000^49 ≤ 42458515232833^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048510281 2000000000 42458515232833 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5027727761/10000000000 : ℝ)^65 ≤ (20083088122907/50000000000000 : ℝ)^49 := by
    have hnat : (5027727761 : ℕ)^65*50000000000000^49 ≤ 20083088122907^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027727761 10000000000 20083088122907 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2673166789/10000000000 : ℝ), (1048510281/2000000000 : ℝ), (5027727761/10000000000 : ℝ)] ![(4343827126679/25000000000000 : ℝ), (42458515232833/100000000000000 : ℝ), (20083088122907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2673166789/10000000000 : ℝ)|^65 ≤ (4343827126679/25000000000000 : ℝ)^49
        have hw : |(-2673166789/10000000000 : ℝ)|=(2673166789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048510281/2000000000 : ℝ)|^65 ≤ (42458515232833/100000000000000 : ℝ)^49
        have hw : |(1048510281/2000000000 : ℝ)|=(1048510281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5027727761/10000000000 : ℝ)|^65 ≤ (20083088122907/50000000000000 : ℝ)^49
        have hw : |(5027727761/10000000000 : ℝ)|=(5027727761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4714264589/10000000000 : ℝ)*x 0 + (-1775443163/10000000000 : ℝ)*x 1 + (6198676353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4714264589/10000000000 : ℝ)^65 ≤ (18439265450181/50000000000000 : ℝ)^49 := by
    have hnat : (4714264589 : ℕ)^65*50000000000000^49 ≤ 18439265450181^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714264589 10000000000 18439265450181 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1775443163/10000000000 : ℝ)^65 ≤ (5048384904443/50000000000000 : ℝ)^49 := by
    have hnat : (1775443163 : ℕ)^65*50000000000000^49 ≤ 5048384904443^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775443163 10000000000 5048384904443 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6198676353/10000000000 : ℝ)^65 ≤ (2651234963893/5000000000000 : ℝ)^49 := by
    have hnat : (6198676353 : ℕ)^65*5000000000000^49 ≤ 2651234963893^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6198676353 10000000000 2651234963893 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4714264589/10000000000 : ℝ), (-1775443163/10000000000 : ℝ), (6198676353/10000000000 : ℝ)] ![(18439265450181/50000000000000 : ℝ), (5048384904443/50000000000000 : ℝ), (2651234963893/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4714264589/10000000000 : ℝ)|^65 ≤ (18439265450181/50000000000000 : ℝ)^49
        have hw : |(4714264589/10000000000 : ℝ)|=(4714264589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1775443163/10000000000 : ℝ)|^65 ≤ (5048384904443/50000000000000 : ℝ)^49
        have hw : |(-1775443163/10000000000 : ℝ)|=(1775443163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6198676353/10000000000 : ℝ)|^65 ≤ (2651234963893/5000000000000 : ℝ)^49
        have hw : |(6198676353/10000000000 : ℝ)|=(6198676353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4716649289/10000000000 : ℝ)*x 0 + (356801463/625000000 : ℝ)*x 1 + (-1229753133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4716649289/10000000000 : ℝ)^65 ≤ (36903279267403/100000000000000 : ℝ)^49 := by
    have hnat : (4716649289 : ℕ)^65*100000000000000^49 ≤ 36903279267403^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4716649289 10000000000 36903279267403 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (356801463/625000000 : ℝ)^65 ≤ (47539173211957/100000000000000 : ℝ)^49 := by
    have hnat : (356801463 : ℕ)^65*100000000000000^49 ≤ 47539173211957^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356801463 625000000 47539173211957 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229753133/5000000000 : ℝ)^65 ≤ (15557547514949/100000000000000 : ℝ)^49 := by
    have hnat : (1229753133 : ℕ)^65*100000000000000^49 ≤ 15557547514949^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229753133 5000000000 15557547514949 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4716649289/10000000000 : ℝ), (356801463/625000000 : ℝ), (-1229753133/5000000000 : ℝ)] ![(36903279267403/100000000000000 : ℝ), (47539173211957/100000000000000 : ℝ), (15557547514949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4716649289/10000000000 : ℝ)|^65 ≤ (36903279267403/100000000000000 : ℝ)^49
        have hw : |(4716649289/10000000000 : ℝ)|=(4716649289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(356801463/625000000 : ℝ)|^65 ≤ (47539173211957/100000000000000 : ℝ)^49
        have hw : |(356801463/625000000 : ℝ)|=(356801463/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1229753133/5000000000 : ℝ)|^65 ≤ (15557547514949/100000000000000 : ℝ)^49
        have hw : |(-1229753133/5000000000 : ℝ)|=(1229753133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5511767409/10000000000 : ℝ)*x 0 + (2329792253/5000000000 : ℝ)*x 1 + (2781216921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5511767409/10000000000 : ℝ)^65 ≤ (5671846241017/12500000000000 : ℝ)^49 := by
    have hnat : (5511767409 : ℕ)^65*12500000000000^49 ≤ 5671846241017^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511767409 10000000000 5671846241017 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2329792253/5000000000 : ℝ)^65 ≤ (18156093162617/50000000000000 : ℝ)^49 := by
    have hnat : (2329792253 : ℕ)^65*50000000000000^49 ≤ 18156093162617^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329792253 5000000000 18156093162617 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2781216921/10000000000 : ℝ)^65 ≤ (18313043732537/100000000000000 : ℝ)^49 := by
    have hnat : (2781216921 : ℕ)^65*100000000000000^49 ≤ 18313043732537^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781216921 10000000000 18313043732537 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5511767409/10000000000 : ℝ), (2329792253/5000000000 : ℝ), (2781216921/10000000000 : ℝ)] ![(5671846241017/12500000000000 : ℝ), (18156093162617/50000000000000 : ℝ), (18313043732537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5511767409/10000000000 : ℝ)|^65 ≤ (5671846241017/12500000000000 : ℝ)^49
        have hw : |(5511767409/10000000000 : ℝ)|=(5511767409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2329792253/5000000000 : ℝ)|^65 ≤ (18156093162617/50000000000000 : ℝ)^49
        have hw : |(2329792253/5000000000 : ℝ)|=(2329792253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2781216921/10000000000 : ℝ)|^65 ≤ (18313043732537/100000000000000 : ℝ)^49
        have hw : |(2781216921/10000000000 : ℝ)|=(2781216921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-243372341/1000000000 : ℝ)*x 0 + (676111003/1250000000 : ℝ)*x 1 + (5050125059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (243372341/1000000000 : ℝ)^65 ≤ (1534157633031/10000000000000 : ℝ)^49 := by
    have hnat : (243372341 : ℕ)^65*10000000000000^49 ≤ 1534157633031^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243372341 1000000000 1534157633031 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676111003/1250000000 : ℝ)^65 ≤ (4425471818189/10000000000000 : ℝ)^49 := by
    have hnat : (676111003 : ℕ)^65*10000000000000^49 ≤ 4425471818189^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676111003 1250000000 4425471818189 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5050125059/10000000000 : ℝ)^65 ≤ (40403705484331/100000000000000 : ℝ)^49 := by
    have hnat : (5050125059 : ℕ)^65*100000000000000^49 ≤ 40403705484331^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5050125059 10000000000 40403705484331 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-243372341/1000000000 : ℝ), (676111003/1250000000 : ℝ), (5050125059/10000000000 : ℝ)] ![(1534157633031/10000000000000 : ℝ), (4425471818189/10000000000000 : ℝ), (40403705484331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-243372341/1000000000 : ℝ)|^65 ≤ (1534157633031/10000000000000 : ℝ)^49
        have hw : |(-243372341/1000000000 : ℝ)|=(243372341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676111003/1250000000 : ℝ)|^65 ≤ (4425471818189/10000000000000 : ℝ)^49
        have hw : |(676111003/1250000000 : ℝ)|=(676111003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5050125059/10000000000 : ℝ)|^65 ≤ (40403705484331/100000000000000 : ℝ)^49
        have hw : |(5050125059/10000000000 : ℝ)|=(5050125059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4566262931/10000000000 : ℝ)*x 0 + (-1978051467/10000000000 : ℝ)*x 1 + (3098090069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4566262931/10000000000 : ℝ)^65 ≤ (4418828488357/12500000000000 : ℝ)^49 := by
    have hnat : (4566262931 : ℕ)^65*12500000000000^49 ≤ 4418828488357^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4566262931 10000000000 4418828488357 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978051467/10000000000 : ℝ)^65 ≤ (11652996495651/100000000000000 : ℝ)^49 := by
    have hnat : (1978051467 : ℕ)^65*100000000000000^49 ≤ 11652996495651^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978051467 10000000000 11652996495651 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3098090069/5000000000 : ℝ)^65 ≤ (5299637557949/10000000000000 : ℝ)^49 := by
    have hnat : (3098090069 : ℕ)^65*10000000000000^49 ≤ 5299637557949^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3098090069 5000000000 5299637557949 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4566262931/10000000000 : ℝ), (-1978051467/10000000000 : ℝ), (3098090069/5000000000 : ℝ)] ![(4418828488357/12500000000000 : ℝ), (11652996495651/100000000000000 : ℝ), (5299637557949/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4566262931/10000000000 : ℝ)|^65 ≤ (4418828488357/12500000000000 : ℝ)^49
        have hw : |(4566262931/10000000000 : ℝ)|=(4566262931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978051467/10000000000 : ℝ)|^65 ≤ (11652996495651/100000000000000 : ℝ)^49
        have hw : |(-1978051467/10000000000 : ℝ)|=(1978051467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3098090069/5000000000 : ℝ)|^65 ≤ (5299637557949/10000000000000 : ℝ)^49
        have hw : |(3098090069/5000000000 : ℝ)|=(3098090069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5049898199/10000000000 : ℝ)*x 0 + (1351625133/2500000000 : ℝ)*x 1 + (-2437109147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5049898199/10000000000 : ℝ)^65 ≤ (1010032446173/2500000000000 : ℝ)^49 := by
    have hnat : (5049898199 : ℕ)^65*2500000000000^49 ≤ 1010032446173^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049898199 10000000000 1010032446173 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351625133/2500000000 : ℝ)^65 ≤ (22114403730727/50000000000000 : ℝ)^49 := by
    have hnat : (1351625133 : ℕ)^65*50000000000000^49 ≤ 22114403730727^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351625133 2500000000 22114403730727 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2437109147/10000000000 : ℝ)^65 ≤ (3073978934971/20000000000000 : ℝ)^49 := by
    have hnat : (2437109147 : ℕ)^65*20000000000000^49 ≤ 3073978934971^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437109147 10000000000 3073978934971 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5049898199/10000000000 : ℝ), (1351625133/2500000000 : ℝ), (-2437109147/10000000000 : ℝ)] ![(1010032446173/2500000000000 : ℝ), (22114403730727/50000000000000 : ℝ), (3073978934971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5049898199/10000000000 : ℝ)|^65 ≤ (1010032446173/2500000000000 : ℝ)^49
        have hw : |(5049898199/10000000000 : ℝ)|=(5049898199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351625133/2500000000 : ℝ)|^65 ≤ (22114403730727/50000000000000 : ℝ)^49
        have hw : |(1351625133/2500000000 : ℝ)|=(1351625133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2437109147/10000000000 : ℝ)|^65 ≤ (3073978934971/20000000000000 : ℝ)^49
        have hw : |(-2437109147/10000000000 : ℝ)|=(2437109147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (748167789/1250000000 : ℝ)*x 0 + (51731603/125000000 : ℝ)*x 1 + (696526641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (748167789/1250000000 : ℝ)^65 ≤ (50617620576659/100000000000000 : ℝ)^49 := by
    have hnat : (748167789 : ℕ)^65*100000000000000^49 ≤ 50617620576659^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748167789 1250000000 50617620576659 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51731603/125000000 : ℝ)^65 ≤ (31026614357283/100000000000000 : ℝ)^49 := by
    have hnat : (51731603 : ℕ)^65*100000000000000^49 ≤ 31026614357283^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51731603 125000000 31026614357283 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696526641/2500000000 : ℝ)^65 ≤ (3671153011019/20000000000000 : ℝ)^49 := by
    have hnat : (696526641 : ℕ)^65*20000000000000^49 ≤ 3671153011019^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696526641 2500000000 3671153011019 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(748167789/1250000000 : ℝ), (51731603/125000000 : ℝ), (696526641/2500000000 : ℝ)] ![(50617620576659/100000000000000 : ℝ), (31026614357283/100000000000000 : ℝ), (3671153011019/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(748167789/1250000000 : ℝ)|^65 ≤ (50617620576659/100000000000000 : ℝ)^49
        have hw : |(748167789/1250000000 : ℝ)|=(748167789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51731603/125000000 : ℝ)|^65 ≤ (31026614357283/100000000000000 : ℝ)^49
        have hw : |(51731603/125000000 : ℝ)|=(51731603/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(696526641/2500000000 : ℝ)|^65 ≤ (3671153011019/20000000000000 : ℝ)^49
        have hw : |(696526641/2500000000 : ℝ)|=(696526641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1225345341/5000000000 : ℝ)*x 0 + (57077147/100000000 : ℝ)*x 1 + (4724949817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1225345341/5000000000 : ℝ)^65 ≤ (7741809911877/50000000000000 : ℝ)^49 := by
    have hnat : (1225345341 : ℕ)^65*50000000000000^49 ≤ 7741809911877^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225345341 5000000000 7741809911877 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57077147/100000000 : ℝ)^65 ≤ (47526926325209/100000000000000 : ℝ)^49 := by
    have hnat : (57077147 : ℕ)^65*100000000000000^49 ≤ 47526926325209^49*100000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57077147 100000000 47526926325209 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4724949817/10000000000 : ℝ)^65 ≤ (7397890765877/20000000000000 : ℝ)^49 := by
    have hnat : (4724949817 : ℕ)^65*20000000000000^49 ≤ 7397890765877^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4724949817 10000000000 7397890765877 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1225345341/5000000000 : ℝ), (57077147/100000000 : ℝ), (4724949817/10000000000 : ℝ)] ![(7741809911877/50000000000000 : ℝ), (47526926325209/100000000000000 : ℝ), (7397890765877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1225345341/5000000000 : ℝ)|^65 ≤ (7741809911877/50000000000000 : ℝ)^49
        have hw : |(-1225345341/5000000000 : ℝ)|=(1225345341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57077147/100000000 : ℝ)|^65 ≤ (47526926325209/100000000000000 : ℝ)^49
        have hw : |(57077147/100000000 : ℝ)|=(57077147/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4724949817/10000000000 : ℝ)|^65 ≤ (7397890765877/20000000000000 : ℝ)^49
        have hw : |(4724949817/10000000000 : ℝ)|=(4724949817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5030545247/10000000000 : ℝ)*x 0 + (-355787473/2000000000 : ℝ)*x 1 + (590164513/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5030545247/10000000000 : ℝ)^65 ≤ (10049009365763/25000000000000 : ℝ)^49 := by
    have hnat : (5030545247 : ℕ)^65*25000000000000^49 ≤ 10049009365763^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030545247 10000000000 10049009365763 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355787473/2000000000 : ℝ)^65 ≤ (10123138005509/100000000000000 : ℝ)^49 := by
    have hnat : (355787473 : ℕ)^65*100000000000000^49 ≤ 10123138005509^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355787473 2000000000 10123138005509 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (590164513/1000000000 : ℝ)^65 ≤ (4968082451397/10000000000000 : ℝ)^49 := by
    have hnat : (590164513 : ℕ)^65*10000000000000^49 ≤ 4968082451397^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590164513 1000000000 4968082451397 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5030545247/10000000000 : ℝ), (-355787473/2000000000 : ℝ), (590164513/1000000000 : ℝ)] ![(10049009365763/25000000000000 : ℝ), (10123138005509/100000000000000 : ℝ), (4968082451397/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5030545247/10000000000 : ℝ)|^65 ≤ (10049009365763/25000000000000 : ℝ)^49
        have hw : |(5030545247/10000000000 : ℝ)|=(5030545247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-355787473/2000000000 : ℝ)|^65 ≤ (10123138005509/100000000000000 : ℝ)^49
        have hw : |(-355787473/2000000000 : ℝ)|=(355787473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(590164513/1000000000 : ℝ)|^65 ≤ (4968082451397/10000000000000 : ℝ)^49
        have hw : |(590164513/1000000000 : ℝ)|=(590164513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (568939777/1250000000 : ℝ)*x 0 + (1426331981/2500000000 : ℝ)*x 1 + (-2664445403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (568939777/1250000000 : ℝ)^65 ≤ (35199285480371/100000000000000 : ℝ)^49 := by
    have hnat : (568939777 : ℕ)^65*100000000000000^49 ≤ 35199285480371^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568939777 1250000000 35199285480371 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426331981/2500000000 : ℝ)^65 ≤ (23750282211143/50000000000000 : ℝ)^49 := by
    have hnat : (1426331981 : ℕ)^65*50000000000000^49 ≤ 23750282211143^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426331981 2500000000 23750282211143 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2664445403/10000000000 : ℝ)^65 ≤ (17300150078681/100000000000000 : ℝ)^49 := by
    have hnat : (2664445403 : ℕ)^65*100000000000000^49 ≤ 17300150078681^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2664445403 10000000000 17300150078681 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(568939777/1250000000 : ℝ), (1426331981/2500000000 : ℝ), (-2664445403/10000000000 : ℝ)] ![(35199285480371/100000000000000 : ℝ), (23750282211143/50000000000000 : ℝ), (17300150078681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(568939777/1250000000 : ℝ)|^65 ≤ (35199285480371/100000000000000 : ℝ)^49
        have hw : |(568939777/1250000000 : ℝ)|=(568939777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426331981/2500000000 : ℝ)|^65 ≤ (23750282211143/50000000000000 : ℝ)^49
        have hw : |(1426331981/2500000000 : ℝ)|=(1426331981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2664445403/10000000000 : ℝ)|^65 ≤ (17300150078681/100000000000000 : ℝ)^49
        have hw : |(-2664445403/10000000000 : ℝ)|=(2664445403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301055_s9_s9_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1504722507/2500000000 : ℝ)*x 0 + (468571073/1250000000 : ℝ)*x 1 + (12685327/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1504722507/2500000000 : ℝ)^65 ≤ (12748578862373/25000000000000 : ℝ)^49 := by
    have hnat : (1504722507 : ℕ)^65*25000000000000^49 ≤ 12748578862373^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504722507 2500000000 12748578862373 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468571073/1250000000 : ℝ)^65 ≤ (27209432834821/100000000000000 : ℝ)^49 := by
    have hnat : (468571073 : ℕ)^65*100000000000000^49 ≤ 27209432834821^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468571073 1250000000 27209432834821 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12685327/40000000 : ℝ)^65 ≤ (10898125851393/50000000000000 : ℝ)^49 := by
    have hnat : (12685327 : ℕ)^65*50000000000000^49 ≤ 10898125851393^49*40000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12685327 40000000 10898125851393 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1504722507/2500000000 : ℝ), (468571073/1250000000 : ℝ), (12685327/40000000 : ℝ)] ![(12748578862373/25000000000000 : ℝ), (27209432834821/100000000000000 : ℝ), (10898125851393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1504722507/2500000000 : ℝ)|^65 ≤ (12748578862373/25000000000000 : ℝ)^49
        have hw : |(1504722507/2500000000 : ℝ)|=(1504722507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(468571073/1250000000 : ℝ)|^65 ≤ (27209432834821/100000000000000 : ℝ)^49
        have hw : |(468571073/1250000000 : ℝ)|=(468571073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12685327/40000000 : ℝ)|^65 ≤ (10898125851393/50000000000000 : ℝ)^49
        have hw : |(12685327/40000000 : ℝ)|=(12685327/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301055_s9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev8 : (0 : ℝ) ≤ ((16633/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16633/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1067/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1067/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33763/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33763/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1251/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1251/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(259/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(259/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5081/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5081/25000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev8 with ⟨ratio_s8_0,ratio_s8_1,ratio_s8_2⟩
  have s9_pow0 : (16633/50000 : ℝ) ^ (129/32 : ℝ) ≤ (1183218226427126251/100000000000000000000 : ℝ) := by
    have hpowers : (16633/50000 : ℝ)^129 ≤ (1183218226427126251/100000000000000000000 : ℝ)^32 := by
      have hnat : (16633 : ℕ)^129*100000000000000000000^32 ≤ 1183218226427126251^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16633 50000 1183218226427126251 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16633/50000 : ℝ)) (X := (1183218226427126251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s9_corner0a : (101183218226427126251/100000000000000000000 : ℝ) ≤ (5014610737574489/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (101183218226427126251/100000000000000000000 : ℝ)^32 ≤ (5014610737574489/5000000000000000 : ℝ)^129 := by
      have hnat : (101183218226427126251 : ℕ)^32*5000000000000000^129 ≤ 5014610737574489^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101183218226427126251 100000000000000000000 5014610737574489 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014610737574489/5000000000000000 : ℝ)) (X := (101183218226427126251/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s9_corner0b : (51183218226427126251/50000000000000000000 : ℝ) ≤ (1005818712346149/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (51183218226427126251/50000000000000000000 : ℝ)^32 ≤ (1005818712346149/1000000000000000 : ℝ)^129 := by
      have hnat : (51183218226427126251 : ℕ)^32*1000000000000000^129 ≤ 1005818712346149^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51183218226427126251 50000000000000000000 1005818712346149 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005818712346149/1000000000000000 : ℝ)) (X := (51183218226427126251/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s9_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(14610737574489/1663300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(452588254883/51978125000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (16633/50000 : ℝ)) (alpha := (14610737574489/1663300000000000 : ℝ)) (beta := (452588254883/51978125000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s9_pow0,s9_corner0a]) (by linarith only [s9_pow0,s9_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16633/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s8_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(14610737574489/1663300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(452588254883/51978125000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s9_pow1 : (1067/3125 : ℝ) ^ (129/32 : ℝ) ≤ (1314236927655317551/100000000000000000000 : ℝ) := by
    have hpowers : (1067/3125 : ℝ)^129 ≤ (1314236927655317551/100000000000000000000 : ℝ)^32 := by
      have hnat : (1067 : ℕ)^129*100000000000000000000^32 ≤ 1314236927655317551^32*3125^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1067 3125 1314236927655317551 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1067/3125 : ℝ)) (X := (1314236927655317551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s9_corner1a : (101314236927655317551/100000000000000000000 : ℝ) ≤ (501622068234181/500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (101314236927655317551/100000000000000000000 : ℝ)^32 ≤ (501622068234181/500000000000000 : ℝ)^129 := by
      have hnat : (101314236927655317551 : ℕ)^32*500000000000000^129 ≤ 501622068234181^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101314236927655317551 100000000000000000000 501622068234181 500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501622068234181/500000000000000 : ℝ)) (X := (101314236927655317551/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s9_corner1b : (51314236927655317551/50000000000000000000 : ℝ) ≤ (1006456782066581/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (51314236927655317551/50000000000000000000 : ℝ)^32 ≤ (1006456782066581/1000000000000000 : ℝ)^129 := by
      have hnat : (51314236927655317551 : ℕ)^32*1000000000000000^129 ≤ 1006456782066581^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51314236927655317551 50000000000000000000 1006456782066581 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006456782066581/1000000000000000 : ℝ)) (X := (51314236927655317551/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s9_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1622068234181/170720000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(3212645598219/341440000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1067/3125 : ℝ)) (alpha := (1622068234181/170720000000000 : ℝ)) (beta := (3212645598219/341440000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s9_pow1,s9_corner1a]) (by linarith only [s9_pow1,s9_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1067/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s8_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1622068234181/170720000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(3212645598219/341440000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s9_pow2 : (33763/100000 : ℝ) ^ (129/32 : ℝ) ≤ (314027662041698307/25000000000000000000 : ℝ) := by
    have hpowers : (33763/100000 : ℝ)^129 ≤ (314027662041698307/25000000000000000000 : ℝ)^32 := by
      have hnat : (33763 : ℕ)^129*25000000000000000000^32 ≤ 314027662041698307^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33763 100000 314027662041698307 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33763/100000 : ℝ)) (X := (314027662041698307/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s9_corner2a : (25314027662041698307/25000000000000000000 : ℝ) ≤ (1253876656430401/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25314027662041698307/25000000000000000000 : ℝ)^32 ≤ (1253876656430401/1250000000000000 : ℝ)^129 := by
      have hnat : (25314027662041698307 : ℕ)^32*1250000000000000^129 ≤ 1253876656430401^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25314027662041698307 25000000000000000000 1253876656430401 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253876656430401/1250000000000000 : ℝ)) (X := (25314027662041698307/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s9_corner2b : (12814027662041698307/12500000000000000000 : ℝ) ≤ (10061738546138207/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (12814027662041698307/12500000000000000000 : ℝ)^32 ≤ (10061738546138207/10000000000000000 : ℝ)^129 := by
      have hnat : (12814027662041698307 : ℕ)^32*10000000000000000^129 ≤ 10061738546138207^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12814027662041698307 12500000000000000000 10061738546138207 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061738546138207/10000000000000000 : ℝ)) (X := (12814027662041698307/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s9_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(3876656430401/422037500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1617120773421/177700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (33763/100000 : ℝ)) (alpha := (3876656430401/422037500000000 : ℝ)) (beta := (1617120773421/177700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s9_pow2,s9_corner2a]) (by linarith only [s9_pow2,s9_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (33763/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s8_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(3876656430401/422037500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1617120773421/177700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s9_0 : ((-2731886657/10000000000 : ℝ)*X 0 0+(683483919/1250000000 : ℝ)*X 0 1+(4747186473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_1 : ((4744521771/10000000000 : ℝ)*X 1 0+(-503487507/2500000000 : ℝ)*X 1 1+(751009281/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_2 : ((1186726453/2500000000 : ℝ)*X 2 0+(2732742327/5000000000 : ℝ)*X 2 1+(-2735215571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_6 : ((5630224327/10000000000 : ℝ)*X 0 0+(2105691907/5000000000 : ℝ)*X 0 1+(3146909319/10000000000 : ℝ)*X 0 2+(5630224327/10000000000 : ℝ)*X 1 0+(2105691907/5000000000 : ℝ)*X 1 1+(3146909319/10000000000 : ℝ)*X 1 2+(5630224327/10000000000 : ℝ)*X 2 0+(2105691907/5000000000 : ℝ)*X 2 1+(3146909319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_7 : ((-2673166789/10000000000 : ℝ)*X 0 0+(1048510281/2000000000 : ℝ)*X 0 1+(5027727761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_8 : ((4714264589/10000000000 : ℝ)*X 1 0+(-1775443163/10000000000 : ℝ)*X 1 1+(6198676353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_9 : ((4716649289/10000000000 : ℝ)*X 2 0+(356801463/625000000 : ℝ)*X 2 1+(-1229753133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_13 : ((5511767409/10000000000 : ℝ)*X 0 0+(2329792253/5000000000 : ℝ)*X 0 1+(2781216921/10000000000 : ℝ)*X 0 2+(5511767409/10000000000 : ℝ)*X 1 0+(2329792253/5000000000 : ℝ)*X 1 1+(2781216921/10000000000 : ℝ)*X 1 2+(5511767409/10000000000 : ℝ)*X 2 0+(2329792253/5000000000 : ℝ)*X 2 1+(2781216921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_14 : ((-243372341/1000000000 : ℝ)*X 0 0+(676111003/1250000000 : ℝ)*X 0 1+(5050125059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_15 : ((4566262931/10000000000 : ℝ)*X 1 0+(-1978051467/10000000000 : ℝ)*X 1 1+(3098090069/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_16 : ((5049898199/10000000000 : ℝ)*X 2 0+(1351625133/2500000000 : ℝ)*X 2 1+(-2437109147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_20 : ((748167789/1250000000 : ℝ)*X 0 0+(51731603/125000000 : ℝ)*X 0 1+(696526641/2500000000 : ℝ)*X 0 2+(748167789/1250000000 : ℝ)*X 1 0+(51731603/125000000 : ℝ)*X 1 1+(696526641/2500000000 : ℝ)*X 1 2+(748167789/1250000000 : ℝ)*X 2 0+(51731603/125000000 : ℝ)*X 2 1+(696526641/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_21 : ((-1225345341/5000000000 : ℝ)*X 0 0+(57077147/100000000 : ℝ)*X 0 1+(4724949817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_22 : ((5030545247/10000000000 : ℝ)*X 1 0+(-355787473/2000000000 : ℝ)*X 1 1+(590164513/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_23 : ((568939777/1250000000 : ℝ)*X 2 0+(1426331981/2500000000 : ℝ)*X 2 1+(-2664445403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s9_27 : ((1504722507/2500000000 : ℝ)*X 0 0+(468571073/1250000000 : ℝ)*X 0 1+(12685327/40000000 : ℝ)*X 0 2+(1504722507/2500000000 : ℝ)*X 1 0+(468571073/1250000000 : ℝ)*X 1 1+(12685327/40000000 : ℝ)*X 1 2+(1504722507/2500000000 : ℝ)*X 2 0+(468571073/1250000000 : ℝ)*X 2 1+(12685327/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301055_s9_s9_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s9_0 : (0 : ℝ) ≤ ((1251/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1251/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8626732866705565296964857/1516847200000000000000000000000 : ℝ) := by norm_num
    linear_combination (2206551294093/1000000000000 : ℝ)*(base49) + (141897/1000000000000 : ℝ)*(base60) + (16116251341577/1000000000000 : ℝ)*(major_s9_0) + (16116251341577/1000000000000 : ℝ)*(major_s9_1) + (16116251341577/1000000000000 : ℝ)*(major_s9_2) + (91055447/1000000000000 : ℝ)*(sp_s9_0) + (89980523/1000000000000 : ℝ)*(sp_s9_2) + (63596231/1000000000000 : ℝ)*(sp_s9_6) + (21337456011401/1000000000000 : ℝ)*(sp_s9_7) + (21337438983697/1000000000000 : ℝ)*(sp_s9_8) + (21337368991781/1000000000000 : ℝ)*(sp_s9_9) + (10894890124313/1000000000000 : ℝ)*(sp_s9_13) + (108083151/1000000000000 : ℝ)*(sp_s9_15) + (5505909/62500000000 : ℝ)*(sp_s9_23) + (340467303767/31250000000 : ℝ)*(f.failure) + (666798345839/31250000000 : ℝ)*(f.sum) + (582724189917446749/28820096800000000000000000000000 : ℝ)*base62 + (41233012976053/177700000000000000000000000 : ℝ)*base64 + (99545332879139/341440000000000000000000000 : ℝ)*base66 + (44121278482011/211018750000000000000000000 : ℝ)*base69 + (695394744489054549/1477842050000000000000000000000 : ℝ)*base70 + (71868562366091/831650000000000000000000000 : ℝ)*base73 + (7277970695459/170720000000000000000000000 : ℝ)*base74 + (48947498981013/1663300000000000000000000000 : ℝ)*base77 + (14879039455216010391/28395857600000000000000000000000 : ℝ)*base78 + (1583/3125000000000000 : ℝ)*base87 + (1583/3125000000000000 : ℝ)*base89 + (1583/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s9_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(259/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(259/1250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5079178640752347756627/1350520000000000000000000000 : ℝ) := by norm_num
    linear_combination (2097085210883/1000000000000 : ℝ)*(base49) + (188191/200000000000 : ℝ)*(base60) + (31389110061/2000000000 : ℝ)*(major_s9_0) + (31389110061/2000000000 : ℝ)*(major_s9_1) + (31389110061/2000000000 : ℝ)*(major_s9_2) + (15428317/500000000000 : ℝ)*(sp_s9_1) + (8137573/250000000000 : ℝ)*(sp_s9_2) + (22206263/500000000000 : ℝ)*(sp_s9_7) + (3733513/100000000000 : ℝ)*(sp_s9_8) + (20779187004757/1000000000000 : ℝ)*(sp_s9_14) + (20779163225519/1000000000000 : ℝ)*(sp_s9_15) + (20779198866991/1000000000000 : ℝ)*(sp_s9_16) + (10609837568923/1000000000000 : ℝ)*(sp_s9_20) + (9955289/250000000000 : ℝ)*(sp_s9_27) + (10609877390079/1000000000000 : ℝ)*(f.failure) + (20779231417283/1000000000000 : ℝ)*(f.sum) + (79043114840985813/288200968000000000000000000000 : ℝ)*base62 + (562744063911/4442500000000000000000000 : ℝ)*base64 + (9987120074869/85360000000000000000000000 : ℝ)*base67 + (156870175740271/337630000000000000000000000 : ℝ)*base68 + (24276311440036431/295568410000000000000000000000 : ℝ)*base71 + (10671736669057/41582500000000000000000000 : ℝ)*base72 + (13471766287951/42680000000000000000000000 : ℝ)*base74 + (23015520739741/83165000000000000000000000 : ℝ)*base76 + (461659817695053981/1419792880000000000000000000000 : ℝ)*base79 + (11499/25000000000000000 : ℝ)*base87 + (11499/25000000000000000 : ℝ)*base89 + (11499/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s9_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5081/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5081/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2853591265603203640604749977/449263983200000000000000000000000 : ℝ) := by norm_num
    linear_combination (2195751/1000000000000 : ℝ)*(base39) + (7086673/1000000000000 : ℝ)*(base40) + (2160050195121/1000000000000 : ℝ)*(base49) + (15689398407397/1000000000000 : ℝ)*(major_s9_0) + (15689398407397/1000000000000 : ℝ)*(major_s9_1) + (15689398407397/1000000000000 : ℝ)*(major_s9_2) + (33816089/100000000000 : ℝ)*(sp_s9_0) + (111060703/500000000000 : ℝ)*(sp_s9_1) + (105135977/1000000000000 : ℝ)*(sp_s9_2) + (276968203/1000000000000 : ℝ)*(sp_s9_20) + (1298254071343/62500000000 : ℝ)*(sp_s9_21) + (20772181180971/1000000000000 : ℝ)*(sp_s9_22) + (20772298166401/1000000000000 : ℝ)*(sp_s9_23) + (1060611442697/100000000000 : ℝ)*(sp_s9_27) + (5303195697587/500000000000 : ℝ)*(f.failure) + (10386201651189/500000000000 : ℝ)*(f.sum) + (1183161897722105381/2620008800000000000000000000000 : ℝ)*base63 + (85781952773537/177700000000000000000000000 : ℝ)*base65 + (483054822049/6208000000000000000000000 : ℝ)*base66 + (1876820055925203/1688150000000000000000000000 : ℝ)*base69 + (439433594461179523/738921025000000000000000000000 : ℝ)*base71 + (293431230178833/415825000000000000000000000 : ℝ)*base73 + (1976550160463/3104000000000000000000000 : ℝ)*base75 + (1598397498128073/1663300000000000000000000000 : ℝ)*base77 + (1417496881080578801/2581441600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (2347/12500000000000000 : ℝ)*base87 + (2347/12500000000000000 : ℝ)*base89 + (2347/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s9_0,ratio_s9_1,ratio_s9_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev8 : (0 : ℝ) ≤ ((16633/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16633/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1067/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1067/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33763/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33763/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1251/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1251/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(259/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(259/1250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5081/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5081/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301055_s9 p hpa hpb X hX hprev8

#print axioms solution

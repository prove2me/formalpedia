-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301059_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:36:08.043885+00:00
-- url     : https://prove2.me/submissions/6ec103c9-608e-4789-8cfd-243c17cb7be3

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
theorem collision_support_c301059_s5_s5_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (376010847/625000000 : ℝ)*x 0 + (1397972869/2500000000 : ℝ)*x 1 + (-336151223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (376010847/625000000 : ℝ)^65 ≤ (12740946894917/25000000000000 : ℝ)^49 := by
    have hnat : (376010847 : ℕ)^65*25000000000000^49 ≤ 12740946894917^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376010847 625000000 12740946894917 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1397972869/2500000000 : ℝ)^65 ≤ (36134243231/78125000000 : ℝ)^49 := by
    have hnat : (1397972869 : ℕ)^65*78125000000^49 ≤ 36134243231^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397972869 2500000000 36134243231 78125000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336151223/5000000000 : ℝ)^65 ≤ (2784381067951/100000000000000 : ℝ)^49 := by
    have hnat : (336151223 : ℕ)^65*100000000000000^49 ≤ 2784381067951^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336151223 5000000000 2784381067951 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(376010847/625000000 : ℝ), (1397972869/2500000000 : ℝ), (-336151223/5000000000 : ℝ)] ![(12740946894917/25000000000000 : ℝ), (36134243231/78125000000 : ℝ), (2784381067951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(376010847/625000000 : ℝ)|^65 ≤ (12740946894917/25000000000000 : ℝ)^49
        have hw : |(376010847/625000000 : ℝ)|=(376010847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1397972869/2500000000 : ℝ)|^65 ≤ (36134243231/78125000000 : ℝ)^49
        have hw : |(1397972869/2500000000 : ℝ)|=(1397972869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-336151223/5000000000 : ℝ)|^65 ≤ (2784381067951/100000000000000 : ℝ)^49
        have hw : |(-336151223/5000000000 : ℝ)|=(336151223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (528103647/1250000000 : ℝ)*x 0 + (643545597/1250000000 : ℝ)*x 1 + (3691635041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528103647/1250000000 : ℝ)^65 ≤ (15943893760171/50000000000000 : ℝ)^49 := by
    have hnat : (528103647 : ℕ)^65*50000000000000^49 ≤ 15943893760171^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528103647 1250000000 15943893760171 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643545597/1250000000 : ℝ)^65 ≤ (8289923241457/20000000000000 : ℝ)^49 := by
    have hnat : (643545597 : ℕ)^65*20000000000000^49 ≤ 8289923241457^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643545597 1250000000 8289923241457 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3691635041/10000000000 : ℝ)^65 ≤ (2666259625303/10000000000000 : ℝ)^49 := by
    have hnat : (3691635041 : ℕ)^65*10000000000000^49 ≤ 2666259625303^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3691635041 10000000000 2666259625303 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528103647/1250000000 : ℝ), (643545597/1250000000 : ℝ), (3691635041/10000000000 : ℝ)] ![(15943893760171/50000000000000 : ℝ), (8289923241457/20000000000000 : ℝ), (2666259625303/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528103647/1250000000 : ℝ)|^65 ≤ (15943893760171/50000000000000 : ℝ)^49
        have hw : |(528103647/1250000000 : ℝ)|=(528103647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643545597/1250000000 : ℝ)|^65 ≤ (8289923241457/20000000000000 : ℝ)^49
        have hw : |(643545597/1250000000 : ℝ)|=(643545597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3691635041/10000000000 : ℝ)|^65 ≤ (2666259625303/10000000000000 : ℝ)^49
        have hw : |(3691635041/10000000000 : ℝ)|=(3691635041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-756505707/2500000000 : ℝ)*x 0 + (274771889/1000000000 : ℝ)*x 1 + (11090497/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (756505707/2500000000 : ℝ)^65 ≤ (1024073400741/5000000000000 : ℝ)^49 := by
    have hnat : (756505707 : ℕ)^65*5000000000000^49 ≤ 1024073400741^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756505707 2500000000 1024073400741 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274771889/1000000000 : ℝ)^65 ≤ (18021028806341/100000000000000 : ℝ)^49 := by
    have hnat : (274771889 : ℕ)^65*100000000000000^49 ≤ 18021028806341^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274771889 1000000000 18021028806341 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11090497/16000000 : ℝ)^65 ≤ (15374375790799/25000000000000 : ℝ)^49 := by
    have hnat : (11090497 : ℕ)^65*25000000000000^49 ≤ 15374375790799^49*16000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11090497 16000000 15374375790799 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-756505707/2500000000 : ℝ), (274771889/1000000000 : ℝ), (11090497/16000000 : ℝ)] ![(1024073400741/5000000000000 : ℝ), (18021028806341/100000000000000 : ℝ), (15374375790799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-756505707/2500000000 : ℝ)|^65 ≤ (1024073400741/5000000000000 : ℝ)^49
        have hw : |(-756505707/2500000000 : ℝ)|=(756505707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274771889/1000000000 : ℝ)|^65 ≤ (18021028806341/100000000000000 : ℝ)^49
        have hw : |(274771889/1000000000 : ℝ)|=(274771889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11090497/16000000 : ℝ)|^65 ≤ (15374375790799/25000000000000 : ℝ)^49
        have hw : |(11090497/16000000 : ℝ)|=(11090497/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1522127149/5000000000 : ℝ)*x 0 + (-2692804607/10000000000 : ℝ)*x 1 + (6958083131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1522127149/5000000000 : ℝ)^65 ≤ (10322660480779/50000000000000 : ℝ)^49 := by
    have hnat : (1522127149 : ℕ)^65*50000000000000^49 ≤ 10322660480779^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522127149 5000000000 10322660480779 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692804607/10000000000 : ℝ)^65 ≤ (17544834655743/100000000000000 : ℝ)^49 := by
    have hnat : (2692804607 : ℕ)^65*100000000000000^49 ≤ 17544834655743^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692804607 10000000000 17544834655743 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6958083131/10000000000 : ℝ)^65 ≤ (61809844367619/100000000000000 : ℝ)^49 := by
    have hnat : (6958083131 : ℕ)^65*100000000000000^49 ≤ 61809844367619^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6958083131 10000000000 61809844367619 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1522127149/5000000000 : ℝ), (-2692804607/10000000000 : ℝ), (6958083131/10000000000 : ℝ)] ![(10322660480779/50000000000000 : ℝ), (17544834655743/100000000000000 : ℝ), (61809844367619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1522127149/5000000000 : ℝ)|^65 ≤ (10322660480779/50000000000000 : ℝ)^49
        have hw : |(1522127149/5000000000 : ℝ)|=(1522127149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2692804607/10000000000 : ℝ)|^65 ≤ (17544834655743/100000000000000 : ℝ)^49
        have hw : |(-2692804607/10000000000 : ℝ)|=(2692804607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6958083131/10000000000 : ℝ)|^65 ≤ (61809844367619/100000000000000 : ℝ)^49
        have hw : |(6958083131/10000000000 : ℝ)|=(6958083131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5605594361/10000000000 : ℝ)*x 0 + (3124288429/5000000000 : ℝ)*x 1 + (-3315091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5605594361/10000000000 : ℝ)^65 ≤ (46402240088807/100000000000000 : ℝ)^49 := by
    have hnat : (5605594361 : ℕ)^65*100000000000000^49 ≤ 46402240088807^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5605594361 10000000000 46402240088807 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3124288429/5000000000 : ℝ)^65 ≤ (53591683363233/100000000000000 : ℝ)^49 := by
    have hnat : (3124288429 : ℕ)^65*100000000000000^49 ≤ 53591683363233^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3124288429 5000000000 53591683363233 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3315091/5000000000 : ℝ)^65 ≤ (1519134469/25000000000000 : ℝ)^49 := by
    have hnat : (3315091 : ℕ)^65*25000000000000^49 ≤ 1519134469^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3315091 5000000000 1519134469 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5605594361/10000000000 : ℝ), (3124288429/5000000000 : ℝ), (-3315091/5000000000 : ℝ)] ![(46402240088807/100000000000000 : ℝ), (53591683363233/100000000000000 : ℝ), (1519134469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5605594361/10000000000 : ℝ)|^65 ≤ (46402240088807/100000000000000 : ℝ)^49
        have hw : |(5605594361/10000000000 : ℝ)|=(5605594361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3124288429/5000000000 : ℝ)|^65 ≤ (53591683363233/100000000000000 : ℝ)^49
        have hw : |(3124288429/5000000000 : ℝ)|=(3124288429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3315091/5000000000 : ℝ)|^65 ≤ (1519134469/25000000000000 : ℝ)^49
        have hw : |(-3315091/5000000000 : ℝ)|=(3315091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1837433083/5000000000 : ℝ)*x 0 + (3345968549/5000000000 : ℝ)*x 1 + (1184610877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1837433083/5000000000 : ℝ)^65 ≤ (26502056588137/100000000000000 : ℝ)^49 := by
    have hnat : (1837433083 : ℕ)^65*100000000000000^49 ≤ 26502056588137^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837433083 5000000000 26502056588137 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3345968549/5000000000 : ℝ)^65 ≤ (58693389292389/100000000000000 : ℝ)^49 := by
    have hnat : (3345968549 : ℕ)^65*100000000000000^49 ≤ 58693389292389^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3345968549 5000000000 58693389292389 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184610877/5000000000 : ℝ)^65 ≤ (14804554114087/100000000000000 : ℝ)^49 := by
    have hnat : (1184610877 : ℕ)^65*100000000000000^49 ≤ 14804554114087^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184610877 5000000000 14804554114087 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1837433083/5000000000 : ℝ), (3345968549/5000000000 : ℝ), (1184610877/5000000000 : ℝ)] ![(26502056588137/100000000000000 : ℝ), (58693389292389/100000000000000 : ℝ), (14804554114087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1837433083/5000000000 : ℝ)|^65 ≤ (26502056588137/100000000000000 : ℝ)^49
        have hw : |(1837433083/5000000000 : ℝ)|=(1837433083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3345968549/5000000000 : ℝ)|^65 ≤ (58693389292389/100000000000000 : ℝ)^49
        have hw : |(3345968549/5000000000 : ℝ)|=(3345968549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1184610877/5000000000 : ℝ)|^65 ≤ (14804554114087/100000000000000 : ℝ)^49
        have hw : |(1184610877/5000000000 : ℝ)|=(1184610877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1371151221/5000000000 : ℝ)*x 0 + (1516425047/5000000000 : ℝ)*x 1 + (6930352937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1371151221/5000000000 : ℝ)^65 ≤ (1123370019121/6250000000000 : ℝ)^49 := by
    have hnat : (1371151221 : ℕ)^65*6250000000000^49 ≤ 1123370019121^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371151221 5000000000 1123370019121 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1516425047/5000000000 : ℝ)^65 ≤ (20542789525741/100000000000000 : ℝ)^49 := by
    have hnat : (1516425047 : ℕ)^65*100000000000000^49 ≤ 20542789525741^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1516425047 5000000000 20542789525741 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6930352937/10000000000 : ℝ)^65 ≤ (30741645075469/50000000000000 : ℝ)^49 := by
    have hnat : (6930352937 : ℕ)^65*50000000000000^49 ≤ 30741645075469^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6930352937 10000000000 30741645075469 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1371151221/5000000000 : ℝ), (1516425047/5000000000 : ℝ), (6930352937/10000000000 : ℝ)] ![(1123370019121/6250000000000 : ℝ), (20542789525741/100000000000000 : ℝ), (30741645075469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1371151221/5000000000 : ℝ)|^65 ≤ (1123370019121/6250000000000 : ℝ)^49
        have hw : |(-1371151221/5000000000 : ℝ)|=(1371151221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1516425047/5000000000 : ℝ)|^65 ≤ (20542789525741/100000000000000 : ℝ)^49
        have hw : |(1516425047/5000000000 : ℝ)|=(1516425047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6930352937/10000000000 : ℝ)|^65 ≤ (30741645075469/50000000000000 : ℝ)^49
        have hw : |(6930352937/10000000000 : ℝ)|=(6930352937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2723359177/10000000000 : ℝ)*x 0 + (-3016384809/10000000000 : ℝ)*x 1 + (3478437919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2723359177/10000000000 : ℝ)^65 ≤ (17809404081209/100000000000000 : ℝ)^49 := by
    have hnat : (2723359177 : ℕ)^65*100000000000000^49 ≤ 17809404081209^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723359177 10000000000 17809404081209 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3016384809/10000000000 : ℝ)^65 ≤ (20394977620021/100000000000000 : ℝ)^49 := by
    have hnat : (3016384809 : ℕ)^65*100000000000000^49 ≤ 20394977620021^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016384809 10000000000 20394977620021 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3478437919/5000000000 : ℝ)^65 ≤ (30897809136503/50000000000000 : ℝ)^49 := by
    have hnat : (3478437919 : ℕ)^65*50000000000000^49 ≤ 30897809136503^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3478437919 5000000000 30897809136503 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2723359177/10000000000 : ℝ), (-3016384809/10000000000 : ℝ), (3478437919/5000000000 : ℝ)] ![(17809404081209/100000000000000 : ℝ), (20394977620021/100000000000000 : ℝ), (30897809136503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2723359177/10000000000 : ℝ)|^65 ≤ (17809404081209/100000000000000 : ℝ)^49
        have hw : |(2723359177/10000000000 : ℝ)|=(2723359177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3016384809/10000000000 : ℝ)|^65 ≤ (20394977620021/100000000000000 : ℝ)^49
        have hw : |(-3016384809/10000000000 : ℝ)|=(3016384809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3478437919/5000000000 : ℝ)|^65 ≤ (30897809136503/50000000000000 : ℝ)^49
        have hw : |(3478437919/5000000000 : ℝ)|=(3478437919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1665823599/2500000000 : ℝ)*x 0 + (2582718199/5000000000 : ℝ)*x 1 + (-7838649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1665823599/2500000000 : ℝ)^65 ≤ (11672074717613/20000000000000 : ℝ)^49 := by
    have hnat : (1665823599 : ℕ)^65*20000000000000^49 ≤ 11672074717613^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665823599 2500000000 11672074717613 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2582718199/5000000000 : ℝ)^65 ≤ (41632038598631/100000000000000 : ℝ)^49 := by
    have hnat : (2582718199 : ℕ)^65*100000000000000^49 ≤ 41632038598631^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582718199 5000000000 41632038598631 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7838649/10000000000 : ℝ)^65 ≤ (7587800459/100000000000000 : ℝ)^49 := by
    have hnat : (7838649 : ℕ)^65*100000000000000^49 ≤ 7587800459^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7838649 10000000000 7587800459 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1665823599/2500000000 : ℝ), (2582718199/5000000000 : ℝ), (-7838649/10000000000 : ℝ)] ![(11672074717613/20000000000000 : ℝ), (41632038598631/100000000000000 : ℝ), (7587800459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1665823599/2500000000 : ℝ)|^65 ≤ (11672074717613/20000000000000 : ℝ)^49
        have hw : |(1665823599/2500000000 : ℝ)|=(1665823599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2582718199/5000000000 : ℝ)|^65 ≤ (41632038598631/100000000000000 : ℝ)^49
        have hw : |(2582718199/5000000000 : ℝ)|=(2582718199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7838649/10000000000 : ℝ)|^65 ≤ (7587800459/100000000000000 : ℝ)^49
        have hw : |(-7838649/10000000000 : ℝ)|=(7838649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1201/10000000000 : ℝ)*x 0 + (1201/10000000000 : ℝ)*x 1 + (999999999/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1201/10000000000 : ℝ)^65 ≤ (1651/2500000000000 : ℝ)^49 := by
    have hnat : (1201 : ℕ)^65*2500000000000^49 ≤ 1651^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201 10000000000 1651 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1201/10000000000 : ℝ)^65 ≤ (1651/2500000000000 : ℝ)^49 := by
    have hnat : (1201 : ℕ)^65*2500000000000^49 ≤ 1651^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201 10000000000 1651 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999999999/1000000000 : ℝ)^65 ≤ (99999999867347/100000000000000 : ℝ)^49 := by
    have hnat : (999999999 : ℕ)^65*100000000000000^49 ≤ 99999999867347^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999999999 1000000000 99999999867347 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1201/10000000000 : ℝ), (1201/10000000000 : ℝ), (999999999/1000000000 : ℝ)] ![(1651/2500000000000 : ℝ), (1651/2500000000000 : ℝ), (99999999867347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1201/10000000000 : ℝ)|^65 ≤ (1651/2500000000000 : ℝ)^49
        have hw : |(-1201/10000000000 : ℝ)|=(1201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1201/10000000000 : ℝ)|^65 ≤ (1651/2500000000000 : ℝ)^49
        have hw : |(1201/10000000000 : ℝ)|=(1201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(999999999/1000000000 : ℝ)|^65 ≤ (99999999867347/100000000000000 : ℝ)^49
        have hw : |(999999999/1000000000 : ℝ)|=(999999999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2915240749/5000000000 : ℝ)*x 0 + (145539231/312500000 : ℝ)*x 1 + (2371588303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2915240749/5000000000 : ℝ)^65 ≤ (48887715442433/100000000000000 : ℝ)^49 := by
    have hnat : (2915240749 : ℕ)^65*100000000000000^49 ≤ 48887715442433^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2915240749 5000000000 48887715442433 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145539231/312500000 : ℝ)^65 ≤ (1451524427543/4000000000000 : ℝ)^49 := by
    have hnat : (145539231 : ℕ)^65*4000000000000^49 ≤ 1451524427543^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145539231 312500000 1451524427543 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2371588303/10000000000 : ℝ)^65 ≤ (1482417385199/10000000000000 : ℝ)^49 := by
    have hnat : (2371588303 : ℕ)^65*10000000000000^49 ≤ 1482417385199^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371588303 10000000000 1482417385199 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2915240749/5000000000 : ℝ), (145539231/312500000 : ℝ), (2371588303/10000000000 : ℝ)] ![(48887715442433/100000000000000 : ℝ), (1451524427543/4000000000000 : ℝ), (1482417385199/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2915240749/5000000000 : ℝ)|^65 ≤ (48887715442433/100000000000000 : ℝ)^49
        have hw : |(2915240749/5000000000 : ℝ)|=(2915240749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(145539231/312500000 : ℝ)|^65 ≤ (1451524427543/4000000000000 : ℝ)^49
        have hw : |(145539231/312500000 : ℝ)|=(145539231/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2371588303/10000000000 : ℝ)|^65 ≤ (1482417385199/10000000000000 : ℝ)^49
        have hw : |(2371588303/10000000000 : ℝ)|=(2371588303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3419892579/10000000000 : ℝ)*x 0 + (3430193013/10000000000 : ℝ)*x 1 + (3041756411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3419892579/10000000000 : ℝ)^65 ≤ (4818182715267/20000000000000 : ℝ)^49 := by
    have hnat : (3419892579 : ℕ)^65*20000000000000^49 ≤ 4818182715267^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3419892579 10000000000 4818182715267 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3430193013/10000000000 : ℝ)^65 ≤ (12093606863789/50000000000000 : ℝ)^49 := by
    have hnat : (3430193013 : ℕ)^65*50000000000000^49 ≤ 12093606863789^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3430193013 10000000000 12093606863789 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3041756411/5000000000 : ℝ)^65 ≤ (6465234084969/12500000000000 : ℝ)^49 := by
    have hnat : (3041756411 : ℕ)^65*12500000000000^49 ≤ 6465234084969^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3041756411 5000000000 6465234084969 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3419892579/10000000000 : ℝ), (3430193013/10000000000 : ℝ), (3041756411/5000000000 : ℝ)] ![(4818182715267/20000000000000 : ℝ), (12093606863789/50000000000000 : ℝ), (6465234084969/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3419892579/10000000000 : ℝ)|^65 ≤ (4818182715267/20000000000000 : ℝ)^49
        have hw : |(-3419892579/10000000000 : ℝ)|=(3419892579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3430193013/10000000000 : ℝ)|^65 ≤ (12093606863789/50000000000000 : ℝ)^49
        have hw : |(3430193013/10000000000 : ℝ)|=(3430193013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3041756411/5000000000 : ℝ)|^65 ≤ (6465234084969/12500000000000 : ℝ)^49
        have hw : |(3041756411/5000000000 : ℝ)|=(3041756411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1678518917/5000000000 : ℝ)*x 0 + (-135028361/400000000 : ℝ)*x 1 + (6180253891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1678518917/5000000000 : ℝ)^65 ≤ (2350533446271/10000000000000 : ℝ)^49 := by
    have hnat : (1678518917 : ℕ)^65*10000000000000^49 ≤ 2350533446271^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678518917 5000000000 2350533446271 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135028361/400000000 : ℝ)^65 ≤ (739965995837/3125000000000 : ℝ)^49 := by
    have hnat : (135028361 : ℕ)^65*3125000000000^49 ≤ 739965995837^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135028361 400000000 739965995837 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6180253891/10000000000 : ℝ)^65 ≤ (10563150731117/20000000000000 : ℝ)^49 := by
    have hnat : (6180253891 : ℕ)^65*20000000000000^49 ≤ 10563150731117^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6180253891 10000000000 10563150731117 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1678518917/5000000000 : ℝ), (-135028361/400000000 : ℝ), (6180253891/10000000000 : ℝ)] ![(2350533446271/10000000000000 : ℝ), (739965995837/3125000000000 : ℝ), (10563150731117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1678518917/5000000000 : ℝ)|^65 ≤ (2350533446271/10000000000000 : ℝ)^49
        have hw : |(1678518917/5000000000 : ℝ)|=(1678518917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135028361/400000000 : ℝ)|^65 ≤ (739965995837/3125000000000 : ℝ)^49
        have hw : |(-135028361/400000000 : ℝ)|=(135028361/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6180253891/10000000000 : ℝ)|^65 ≤ (10563150731117/20000000000000 : ℝ)^49
        have hw : |(6180253891/10000000000 : ℝ)|=(6180253891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (912612681/1250000000 : ℝ)*x 0 + (4375339849/10000000000 : ℝ)*x 1 + (-120611613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (912612681/1250000000 : ℝ)^65 ≤ (65881689285573/100000000000000 : ℝ)^49 := by
    have hnat : (912612681 : ℕ)^65*100000000000000^49 ≤ 65881689285573^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912612681 1250000000 65881689285573 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4375339849/10000000000 : ℝ)^65 ≤ (2087714799733/6250000000000 : ℝ)^49 := by
    have hnat : (4375339849 : ℕ)^65*6250000000000^49 ≤ 2087714799733^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375339849 10000000000 2087714799733 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120611613/5000000000 : ℝ)^65 ≤ (357436954283/50000000000000 : ℝ)^49 := by
    have hnat : (120611613 : ℕ)^65*50000000000000^49 ≤ 357436954283^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120611613 5000000000 357436954283 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(912612681/1250000000 : ℝ), (4375339849/10000000000 : ℝ), (-120611613/5000000000 : ℝ)] ![(65881689285573/100000000000000 : ℝ), (2087714799733/6250000000000 : ℝ), (357436954283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(912612681/1250000000 : ℝ)|^65 ≤ (65881689285573/100000000000000 : ℝ)^49
        have hw : |(912612681/1250000000 : ℝ)|=(912612681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4375339849/10000000000 : ℝ)|^65 ≤ (2087714799733/6250000000000 : ℝ)^49
        have hw : |(4375339849/10000000000 : ℝ)|=(4375339849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120611613/5000000000 : ℝ)|^65 ≤ (357436954283/50000000000000 : ℝ)^49
        have hw : |(-120611613/5000000000 : ℝ)|=(120611613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301059_s5_s5_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (80545893/400000000 : ℝ)*x 0 + (30025631/39062500 : ℝ)*x 1 + (672786541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80545893/400000000 : ℝ)^65 ≤ (1193198465247/10000000000000 : ℝ)^49 := by
    have hnat : (80545893 : ℕ)^65*10000000000000^49 ≤ 1193198465247^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80545893 400000000 1193198465247 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30025631/39062500 : ℝ)^65 ≤ (564300104527/800000000000 : ℝ)^49 := by
    have hnat : (30025631 : ℕ)^65*800000000000^49 ≤ 564300104527^49*39062500^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30025631 39062500 564300104527 800000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672786541/2500000000 : ℝ)^65 ≤ (17530502266743/100000000000000 : ℝ)^49 := by
    have hnat : (672786541 : ℕ)^65*100000000000000^49 ≤ 17530502266743^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672786541 2500000000 17530502266743 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80545893/400000000 : ℝ), (30025631/39062500 : ℝ), (672786541/2500000000 : ℝ)] ![(1193198465247/10000000000000 : ℝ), (564300104527/800000000000 : ℝ), (17530502266743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80545893/400000000 : ℝ)|^65 ≤ (1193198465247/10000000000000 : ℝ)^49
        have hw : |(80545893/400000000 : ℝ)|=(80545893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30025631/39062500 : ℝ)|^65 ≤ (564300104527/800000000000 : ℝ)^49
        have hw : |(30025631/39062500 : ℝ)|=(30025631/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672786541/2500000000 : ℝ)|^65 ≤ (17530502266743/100000000000000 : ℝ)^49
        have hw : |(672786541/2500000000 : ℝ)|=(672786541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301059_s5 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((76671/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76671/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18759/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18759/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6389/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(6389/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((28449/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28449/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54773/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54773/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(24513/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(24513/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (76671/100000 : ℝ) ^ (129/32 : ℝ) ≤ (8567601183305179261/25000000000000000000 : ℝ) := by
    have hpowers : (76671/100000 : ℝ)^129 ≤ (8567601183305179261/25000000000000000000 : ℝ)^32 := by
      have hnat : (76671 : ℕ)^129*25000000000000000000^32 ≤ 8567601183305179261^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76671 100000 8567601183305179261 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76671/100000 : ℝ)) (X := (8567601183305179261/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0a : (33567601183305179261/25000000000000000000 : ℝ) ≤ (10758384226307927/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (33567601183305179261/25000000000000000000 : ℝ)^32 ≤ (10758384226307927/10000000000000000 : ℝ)^129 := by
      have hnat : (33567601183305179261 : ℕ)^32*10000000000000000^129 ≤ 10758384226307927^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33567601183305179261 25000000000000000000 10758384226307927 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10758384226307927/10000000000000000 : ℝ)) (X := (33567601183305179261/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0b : (21067601183305179261/12500000000000000000 : ℝ) ≤ (5691240288886419/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (21067601183305179261/12500000000000000000 : ℝ)^32 ≤ (5691240288886419/5000000000000000 : ℝ)^129 := by
      have hnat : (21067601183305179261 : ℕ)^32*5000000000000000^129 ≤ 5691240288886419^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21067601183305179261 12500000000000000000 5691240288886419 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5691240288886419/5000000000000000 : ℝ)) (X := (21067601183305179261/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(758384226307927/7667100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(624096351464911/7667100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (76671/100000 : ℝ)) (alpha := (758384226307927/7667100000000000 : ℝ)) (beta := (624096351464911/7667100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (76671/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(758384226307927/7667100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(624096351464911/7667100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (18759/25000 : ℝ) ^ (129/32 : ℝ) ≤ (7854542336557592941/25000000000000000000 : ℝ) := by
    have hpowers : (18759/25000 : ℝ)^129 ≤ (7854542336557592941/25000000000000000000 : ℝ)^32 := by
      have hnat : (18759 : ℕ)^129*25000000000000000000^32 ≤ 7854542336557592941^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18759 25000 7854542336557592941 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18759/25000 : ℝ)) (X := (7854542336557592941/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1a : (32854542336557592941/25000000000000000000 : ℝ) ≤ (10701234991088843/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (32854542336557592941/25000000000000000000 : ℝ)^32 ≤ (10701234991088843/10000000000000000 : ℝ)^129 := by
      have hnat : (32854542336557592941 : ℕ)^32*10000000000000000^129 ≤ 10701234991088843^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32854542336557592941 25000000000000000000 10701234991088843 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10701234991088843/10000000000000000 : ℝ)) (X := (32854542336557592941/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1b : (20354542336557592941/12500000000000000000 : ℝ) ≤ (11285672971517399/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (20354542336557592941/12500000000000000000 : ℝ)^32 ≤ (11285672971517399/10000000000000000 : ℝ)^129 := by
      have hnat : (20354542336557592941 : ℕ)^32*10000000000000000^129 ≤ 11285672971517399^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20354542336557592941 12500000000000000000 11285672971517399 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11285672971517399/10000000000000000 : ℝ)) (X := (20354542336557592941/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(701234991088843/7503600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(48703165035713/625300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (18759/25000 : ℝ)) (alpha := (701234991088843/7503600000000000 : ℝ)) (beta := (48703165035713/625300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (18759/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(701234991088843/7503600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(48703165035713/625300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (6389/12500 : ℝ) ^ (129/32 : ℝ) ≤ (835396888467535529/12500000000000000000 : ℝ) := by
    have hpowers : (6389/12500 : ℝ)^129 ≤ (835396888467535529/12500000000000000000 : ℝ)^32 := by
      have hnat : (6389 : ℕ)^129*12500000000000000000^32 ≤ 835396888467535529^32*12500^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6389 12500 835396888467535529 12500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6389/12500 : ℝ)) (X := (835396888467535529/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2a : (13335396888467535529/12500000000000000000 : ℝ) ≤ (10161774042377473/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (13335396888467535529/12500000000000000000 : ℝ)^32 ≤ (10161774042377473/10000000000000000 : ℝ)^129 := by
      have hnat : (13335396888467535529 : ℕ)^32*10000000000000000^129 ≤ 10161774042377473^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13335396888467535529 12500000000000000000 10161774042377473 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10161774042377473/10000000000000000 : ℝ)) (X := (13335396888467535529/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2b : (7085396888467535529/6250000000000000000 : ℝ) ≤ (10316097824326071/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (7085396888467535529/6250000000000000000 : ℝ)^32 ≤ (10316097824326071/10000000000000000 : ℝ)^129 := by
      have hnat : (7085396888467535529 : ℕ)^32*10000000000000000^129 ≤ 10316097824326071^129*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7085396888467535529 6250000000000000000 10316097824326071 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10316097824326071/10000000000000000 : ℝ)) (X := (7085396888467535529/6250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(161774042377473/5111200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(77161890974299/2555600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (6389/12500 : ℝ)) (alpha := (161774042377473/5111200000000000 : ℝ)) (beta := (77161890974299/2555600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (6389/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(161774042377473/5111200000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(77161890974299/2555600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_2 : ((376010847/625000000 : ℝ)*X 2 0+(1397972869/2500000000 : ℝ)*X 2 1+(-336151223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((528103647/1250000000 : ℝ)*X 0 0+(643545597/1250000000 : ℝ)*X 0 1+(3691635041/10000000000 : ℝ)*X 0 2+(528103647/1250000000 : ℝ)*X 1 0+(643545597/1250000000 : ℝ)*X 1 1+(3691635041/10000000000 : ℝ)*X 1 2+(528103647/1250000000 : ℝ)*X 2 0+(643545597/1250000000 : ℝ)*X 2 1+(3691635041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-756505707/2500000000 : ℝ)*X 0 0+(274771889/1000000000 : ℝ)*X 0 1+(11090497/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((1522127149/5000000000 : ℝ)*X 1 0+(-2692804607/10000000000 : ℝ)*X 1 1+(6958083131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((5605594361/10000000000 : ℝ)*X 2 0+(3124288429/5000000000 : ℝ)*X 2 1+(-3315091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((1837433083/5000000000 : ℝ)*X 0 0+(3345968549/5000000000 : ℝ)*X 0 1+(1184610877/5000000000 : ℝ)*X 0 2+(1837433083/5000000000 : ℝ)*X 1 0+(3345968549/5000000000 : ℝ)*X 1 1+(1184610877/5000000000 : ℝ)*X 1 2+(1837433083/5000000000 : ℝ)*X 2 0+(3345968549/5000000000 : ℝ)*X 2 1+(1184610877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-1371151221/5000000000 : ℝ)*X 0 0+(1516425047/5000000000 : ℝ)*X 0 1+(6930352937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((2723359177/10000000000 : ℝ)*X 1 0+(-3016384809/10000000000 : ℝ)*X 1 1+(3478437919/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((1665823599/2500000000 : ℝ)*X 2 0+(2582718199/5000000000 : ℝ)*X 2 1+(-7838649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_19 : ((-1201/10000000000 : ℝ)*X 0 0+(1201/10000000000 : ℝ)*X 0 1+(999999999/1000000000 : ℝ)*X 0 2+(-1201/10000000000 : ℝ)*X 1 0+(1201/10000000000 : ℝ)*X 1 1+(999999999/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_19 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((2915240749/5000000000 : ℝ)*X 0 0+(145539231/312500000 : ℝ)*X 0 1+(2371588303/10000000000 : ℝ)*X 0 2+(2915240749/5000000000 : ℝ)*X 1 0+(145539231/312500000 : ℝ)*X 1 1+(2371588303/10000000000 : ℝ)*X 1 2+(2915240749/5000000000 : ℝ)*X 2 0+(145539231/312500000 : ℝ)*X 2 1+(2371588303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-3419892579/10000000000 : ℝ)*X 0 0+(3430193013/10000000000 : ℝ)*X 0 1+(3041756411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((1678518917/5000000000 : ℝ)*X 1 0+(-135028361/400000000 : ℝ)*X 1 1+(6180253891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((912612681/1250000000 : ℝ)*X 2 0+(4375339849/10000000000 : ℝ)*X 2 1+(-120611613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((80545893/400000000 : ℝ)*X 0 0+(30025631/39062500 : ℝ)*X 0 1+(672786541/2500000000 : ℝ)*X 0 2+(80545893/400000000 : ℝ)*X 1 0+(30025631/39062500 : ℝ)*X 1 1+(672786541/2500000000 : ℝ)*X 1 2+(80545893/400000000 : ℝ)*X 2 0+(30025631/39062500 : ℝ)*X 2 1+(672786541/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301059_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((28449/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28449/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (207737953278731670095999587739/51050640363450000000000000000000000 : ℝ) := by norm_num
    linear_combination (685531/500000000000 : ℝ)*(base19) + (28589/15625000000 : ℝ)*(base53) + (73991627353/62500000000 : ℝ)*(base60) + (2765893733507/500000000000 : ℝ)*(major_s5_0) + (2765893733507/500000000000 : ℝ)*(major_s5_1) + (1382959098177/250000000000 : ℝ)*(major_s5_2) + (879803/62500000000 : ℝ)*(sp_s5_2) + (328031/200000000000 : ℝ)*(sp_s5_6) + (7323957170817/1000000000000 : ℝ)*(sp_s5_7) + (1464791159951/200000000000 : ℝ)*(sp_s5_8) + (3661972461833/500000000000 : ℝ)*(sp_s5_9) + (3739595353423/1000000000000 : ℝ)*(sp_s5_13) + (5075539/100000000000 : ℝ)*(sp_s5_19) + (17583511/1000000000000 : ℝ)*(sp_s5_27) + (373961457709/100000000000 : ℝ)*(f.failure) + (3661979500257/500000000000 : ℝ)*(f.sum) + (416044365323286839/2397025020000000000000000000000 : ℝ)*base62 + (151779971329423/638900000000000000000000000 : ℝ)*base65 + (236780115215601/312650000000000000000000000 : ℝ)*base67 + (141898700672661/1277800000000000000000000000 : ℝ)*base68 + (73192118757008953/391880815200000000000000000000 : ℝ)*base71 + (3441519942157247/3833550000000000000000000000 : ℝ)*base73 + (100646906719699/3751800000000000000000000000 : ℝ)*base74 + (920855296821359/3833550000000000000000000000 : ℝ)*base77 + (5017887457700432327/23971188150000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1529/2500000000000000 : ℝ)*base87 + (1529/2500000000000000 : ℝ)*base89 + (1529/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54773/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54773/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (446271020993637046755304867343/27227008193840000000000000000000000 : ℝ) := by norm_num
    linear_combination (537143/1000000000000 : ℝ)*(base19) + (18471/5000000000 : ℝ)*(base53) + (583986150599/500000000000 : ℝ)*(base60) + (136682406687/25000000000 : ℝ)*(major_s5_0) + (136682406687/25000000000 : ℝ)*(major_s5_1) + (5467450848761/1000000000000 : ℝ)*(major_s5_2) + (19273669/1000000000000 : ℝ)*(sp_s5_6) + (175891691/1000000000000 : ℝ)*(sp_s5_7) + (904798803891/125000000000 : ℝ)*(sp_s5_14) + (1809641446419/250000000000 : ℝ)*(sp_s5_15) + (90480720609/12500000000 : ℝ)*(sp_s5_16) + (158275481/1000000000000 : ℝ)*(sp_s5_19) + (3695997780683/1000000000000 : ℝ)*(sp_s5_20) + (56184149/500000000000 : ℝ)*(sp_s5_23) + (231001065897/62500000000 : ℝ)*(f.failure) + (7238570017019/1000000000000 : ℝ)*(f.sum) + (14640461669855124251/31960333600000000000000000000000 : ℝ)*base63 + (1043405324682059/2555600000000000000000000000 : ℝ)*base65 + (13272542268437/62530000000000000000000000 : ℝ)*base67 + (2135154378898167/5111200000000000000000000000 : ℝ)*base69 + (30340700471286425303/65313469200000000000000000000000 : ℝ)*base71 + (12134257304821/63892500000000000000000000 : ℝ)*base73 + (51160766378041/62530000000000000000000000 : ℝ)*base75 + (86988609089969/127785000000000000000000000 : ℝ)*base77 + (45919792748752073/799039605000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (543/1562500000000000 : ℝ)*base86 + (543/1562500000000000 : ℝ)*base88 + (543/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(24513/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(24513/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25399115106754133868414218931/4254220030287500000000000000000000 : ℝ) := by norm_num
    linear_combination (647397/1000000000000 : ℝ)*(base8) + (613767/250000000000 : ℝ)*(base11) + (5611969869/200000000000 : ℝ)*(base50) + (42566676943/250000000000 : ℝ)*(base60) + (1509028488081/500000000000 : ℝ)*(major_s5_0) + (1509028488081/500000000000 : ℝ)*(major_s5_1) + (1509028488081/500000000000 : ℝ)*(major_s5_2) + (6061829/250000000000 : ℝ)*(sp_s5_2) + (13707683/250000000000 : ℝ)*(sp_s5_13) + (40889/976562500 : ℝ)*(sp_s5_16) + (24973959151/6250000000 : ℝ)*(sp_s5_21) + (31966692533/8000000000 : ℝ)*(sp_s5_22) + (998942612243/250000000000 : ℝ)*(sp_s5_23) + (2040220564851/1000000000000 : ℝ)*(sp_s5_27) + (2040275395583/1000000000000 : ℝ)*(f.failure) + (31966692533/8000000000 : ℝ)*(f.sum) + (4086205222857351909/15980166800000000000000000000000 : ℝ)*base63 + (902269099216341/1277800000000000000000000000 : ℝ)*base64 + (120132069063427/312650000000000000000000000 : ℝ)*base66 + (1885331983643033/2555600000000000000000000000 : ℝ)*base68 + (2171693691392240171/10885578200000000000000000000000 : ℝ)*base70 + (125345468115583/212975000000000000000000000 : ℝ)*base72 + (334363507329901/1250600000000000000000000000 : ℝ)*base75 + (13228709242163/425950000000000000000000000 : ℝ)*base77 + (334529763088478773/1331732675000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (4923/25000000000000000 : ℝ)*base87 + (4923/25000000000000000 : ℝ)*base89 + (4923/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((76671/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76671/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18759/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18759/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6389/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(6389/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((28449/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28449/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54773/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54773/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(24513/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(24513/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301059_s5 p hpa hpb X hX hprev4

#print axioms solution

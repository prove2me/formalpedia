-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:01:57.370192+00:00
-- url     : https://prove2.me/submissions/43840a56-bb39-4e67-9d6d-64a462681427

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
theorem collision_support_c311062_s2_s2_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-70124347/400000000 : ℝ)*x 0 + (192463/390625 : ℝ)*x 1 + (-1437502821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70124347/400000000 : ℝ)^9 ≤ (10659926771367/100000000000000 : ℝ)^7 := by
    have hnat : (70124347 : ℕ)^9*100000000000000^7 ≤ 10659926771367^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70124347 400000000 10659926771367 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192463/390625 : ℝ)^9 ≤ (1257780954027/3125000000000 : ℝ)^7 := by
    have hnat : (192463 : ℕ)^9*3125000000000^7 ≤ 1257780954027^7*390625^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192463 390625 1257780954027 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1437502821/2500000000 : ℝ)^9 ≤ (49091082682489/100000000000000 : ℝ)^7 := by
    have hnat : (1437502821 : ℕ)^9*100000000000000^7 ≤ 49091082682489^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437502821 2500000000 49091082682489 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-70124347/400000000 : ℝ), (192463/390625 : ℝ), (-1437502821/2500000000 : ℝ)] ![(10659926771367/100000000000000 : ℝ), (1257780954027/3125000000000 : ℝ), (49091082682489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-70124347/400000000 : ℝ)|^9 ≤ (10659926771367/100000000000000 : ℝ)^7
        have hw : |(-70124347/400000000 : ℝ)|=(70124347/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192463/390625 : ℝ)|^9 ≤ (1257780954027/3125000000000 : ℝ)^7
        have hw : |(192463/390625 : ℝ)|=(192463/390625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1437502821/2500000000 : ℝ)|^9 ≤ (49091082682489/100000000000000 : ℝ)^7
        have hw : |(-1437502821/2500000000 : ℝ)|=(1437502821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4931955169/10000000000 : ℝ)*x 0 + (-878485547/5000000000 : ℝ)*x 1 + (-5742566777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4931955169/10000000000 : ℝ)^9 ≤ (40300487294741/100000000000000 : ℝ)^7 := by
    have hnat : (4931955169 : ℕ)^9*100000000000000^7 ≤ 40300487294741^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4931955169 10000000000 40300487294741 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878485547/5000000000 : ℝ)^9 ≤ (10690132257771/100000000000000 : ℝ)^7 := by
    have hnat : (878485547 : ℕ)^9*100000000000000^7 ≤ 10690132257771^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878485547 5000000000 10690132257771 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5742566777/10000000000 : ℝ)^9 ≤ (49009380441709/100000000000000 : ℝ)^7 := by
    have hnat : (5742566777 : ℕ)^9*100000000000000^7 ≤ 49009380441709^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5742566777 10000000000 49009380441709 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4931955169/10000000000 : ℝ), (-878485547/5000000000 : ℝ), (-5742566777/10000000000 : ℝ)] ![(40300487294741/100000000000000 : ℝ), (10690132257771/100000000000000 : ℝ), (49009380441709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4931955169/10000000000 : ℝ)|^9 ≤ (40300487294741/100000000000000 : ℝ)^7
        have hw : |(4931955169/10000000000 : ℝ)|=(4931955169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-878485547/5000000000 : ℝ)|^9 ≤ (10690132257771/100000000000000 : ℝ)^7
        have hw : |(-878485547/5000000000 : ℝ)|=(878485547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5742566777/10000000000 : ℝ)|^9 ≤ (49009380441709/100000000000000 : ℝ)^7
        have hw : |(-5742566777/10000000000 : ℝ)|=(5742566777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1292518991/2500000000 : ℝ)*x 0 + (5176125251/10000000000 : ℝ)*x 1 + (1101388987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292518991/2500000000 : ℝ)^9 ≤ (8563846972013/20000000000000 : ℝ)^7 := by
    have hnat : (1292518991 : ℕ)^9*20000000000000^7 ≤ 8563846972013^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292518991 2500000000 8563846972013 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176125251/10000000000 : ℝ)^9 ≤ (4288366116203/10000000000000 : ℝ)^7 := by
    have hnat : (5176125251 : ℕ)^9*10000000000000^7 ≤ 4288366116203^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176125251 10000000000 4288366116203 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101388987/5000000000 : ℝ)^9 ≤ (14297103966157/100000000000000 : ℝ)^7 := by
    have hnat : (1101388987 : ℕ)^9*100000000000000^7 ≤ 14297103966157^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101388987 5000000000 14297103966157 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292518991/2500000000 : ℝ), (5176125251/10000000000 : ℝ), (1101388987/5000000000 : ℝ)] ![(8563846972013/20000000000000 : ℝ), (4288366116203/10000000000000 : ℝ), (14297103966157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292518991/2500000000 : ℝ)|^9 ≤ (8563846972013/20000000000000 : ℝ)^7
        have hw : |(1292518991/2500000000 : ℝ)|=(1292518991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176125251/10000000000 : ℝ)|^9 ≤ (4288366116203/10000000000000 : ℝ)^7
        have hw : |(5176125251/10000000000 : ℝ)|=(5176125251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101388987/5000000000 : ℝ)|^9 ≤ (14297103966157/100000000000000 : ℝ)^7
        have hw : |(1101388987/5000000000 : ℝ)|=(1101388987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-667298711/5000000000 : ℝ)*x 0 + (2182314739/5000000000 : ℝ)*x 1 + (-655094757/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667298711/5000000000 : ℝ)^9 ≤ (1501344501393/20000000000000 : ℝ)^7 := by
    have hnat : (667298711 : ℕ)^9*20000000000000^7 ≤ 1501344501393^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667298711 5000000000 1501344501393 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182314739/5000000000 : ℝ)^9 ≤ (17220478270899/50000000000000 : ℝ)^7 := by
    have hnat : (2182314739 : ℕ)^9*50000000000000^7 ≤ 17220478270899^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182314739 5000000000 17220478270899 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655094757/1000000000 : ℝ)^9 ≤ (29026160464251/50000000000000 : ℝ)^7 := by
    have hnat : (655094757 : ℕ)^9*50000000000000^7 ≤ 29026160464251^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655094757 1000000000 29026160464251 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-667298711/5000000000 : ℝ), (2182314739/5000000000 : ℝ), (-655094757/1000000000 : ℝ)] ![(1501344501393/20000000000000 : ℝ), (17220478270899/50000000000000 : ℝ), (29026160464251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-667298711/5000000000 : ℝ)|^9 ≤ (1501344501393/20000000000000 : ℝ)^7
        have hw : |(-667298711/5000000000 : ℝ)|=(667298711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2182314739/5000000000 : ℝ)|^9 ≤ (17220478270899/50000000000000 : ℝ)^7
        have hw : |(2182314739/5000000000 : ℝ)|=(2182314739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-655094757/1000000000 : ℝ)|^9 ≤ (29026160464251/50000000000000 : ℝ)^7
        have hw : |(-655094757/1000000000 : ℝ)|=(655094757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (118860761/250000000 : ℝ)*x 0 + (-447973223/5000000000 : ℝ)*x 1 + (-1615872877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118860761/250000000 : ℝ)^9 ≤ (38445093879743/100000000000000 : ℝ)^7 := by
    have hnat : (118860761 : ℕ)^9*100000000000000^7 ≤ 38445093879743^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118860761 250000000 38445093879743 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447973223/5000000000 : ℝ)^9 ≤ (562139468441/12500000000000 : ℝ)^7 := by
    have hnat : (447973223 : ℕ)^9*12500000000000^7 ≤ 562139468441^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447973223 5000000000 562139468441 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1615872877/2500000000 : ℝ)^9 ≤ (28528895179163/50000000000000 : ℝ)^7 := by
    have hnat : (1615872877 : ℕ)^9*50000000000000^7 ≤ 28528895179163^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1615872877 2500000000 28528895179163 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(118860761/250000000 : ℝ), (-447973223/5000000000 : ℝ), (-1615872877/2500000000 : ℝ)] ![(38445093879743/100000000000000 : ℝ), (562139468441/12500000000000 : ℝ), (28528895179163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(118860761/250000000 : ℝ)|^9 ≤ (38445093879743/100000000000000 : ℝ)^7
        have hw : |(118860761/250000000 : ℝ)|=(118860761/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447973223/5000000000 : ℝ)|^9 ≤ (562139468441/12500000000000 : ℝ)^7
        have hw : |(-447973223/5000000000 : ℝ)|=(447973223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1615872877/2500000000 : ℝ)|^9 ≤ (28528895179163/50000000000000 : ℝ)^7
        have hw : |(-1615872877/2500000000 : ℝ)|=(1615872877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2385561911/5000000000 : ℝ)*x 0 + (316117809/500000000 : ℝ)*x 1 + (1109577611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2385561911/5000000000 : ℝ)^9 ≤ (19309366750491/50000000000000 : ℝ)^7 := by
    have hnat : (2385561911 : ℕ)^9*50000000000000^7 ≤ 19309366750491^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385561911 5000000000 19309366750491 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316117809/500000000 : ℝ)^9 ≤ (27730470429209/50000000000000 : ℝ)^7 := by
    have hnat : (316117809 : ℕ)^9*50000000000000^7 ≤ 27730470429209^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316117809 500000000 27730470429209 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1109577611/10000000000 : ℝ)^9 ≤ (5920325637/100000000000 : ℝ)^7 := by
    have hnat : (1109577611 : ℕ)^9*100000000000^7 ≤ 5920325637^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109577611 10000000000 5920325637 100000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2385561911/5000000000 : ℝ), (316117809/500000000 : ℝ), (1109577611/10000000000 : ℝ)] ![(19309366750491/50000000000000 : ℝ), (27730470429209/50000000000000 : ℝ), (5920325637/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2385561911/5000000000 : ℝ)|^9 ≤ (19309366750491/50000000000000 : ℝ)^7
        have hw : |(2385561911/5000000000 : ℝ)|=(2385561911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(316117809/500000000 : ℝ)|^9 ≤ (27730470429209/50000000000000 : ℝ)^7
        have hw : |(316117809/500000000 : ℝ)|=(316117809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1109577611/10000000000 : ℝ)|^9 ≤ (5920325637/100000000000 : ℝ)^7
        have hw : |(1109577611/10000000000 : ℝ)|=(1109577611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (503471383/1000000000 : ℝ)*x 0 + (1275979119/2000000000 : ℝ)*x 1 + (-568541571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503471383/1000000000 : ℝ)^9 ≤ (41383262967791/100000000000000 : ℝ)^7 := by
    have hnat : (503471383 : ℕ)^9*100000000000000^7 ≤ 41383262967791^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503471383 1000000000 41383262967791 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1275979119/2000000000 : ℝ)^9 ≤ (2805537157833/5000000000000 : ℝ)^7 := by
    have hnat : (1275979119 : ℕ)^9*5000000000000^7 ≤ 2805537157833^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275979119 2000000000 2805537157833 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568541571/10000000000 : ℝ)^9 ≤ (156624616707/6250000000000 : ℝ)^7 := by
    have hnat : (568541571 : ℕ)^9*6250000000000^7 ≤ 156624616707^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568541571 10000000000 156624616707 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(503471383/1000000000 : ℝ), (1275979119/2000000000 : ℝ), (-568541571/10000000000 : ℝ)] ![(41383262967791/100000000000000 : ℝ), (2805537157833/5000000000000 : ℝ), (156624616707/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(503471383/1000000000 : ℝ)|^9 ≤ (41383262967791/100000000000000 : ℝ)^7
        have hw : |(503471383/1000000000 : ℝ)|=(503471383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1275979119/2000000000 : ℝ)|^9 ≤ (2805537157833/5000000000000 : ℝ)^7
        have hw : |(1275979119/2000000000 : ℝ)|=(1275979119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-568541571/10000000000 : ℝ)|^9 ≤ (156624616707/6250000000000 : ℝ)^7
        have hw : |(-568541571/10000000000 : ℝ)|=(568541571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-839296587/10000000000 : ℝ)*x 0 + (4700155687/10000000000 : ℝ)*x 1 + (-1636223807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839296587/10000000000 : ℝ)^9 ≤ (2067439144379/50000000000000 : ℝ)^7 := by
    have hnat : (839296587 : ℕ)^9*50000000000000^7 ≤ 2067439144379^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839296587 10000000000 2067439144379 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4700155687/10000000000 : ℝ)^9 ≤ (7576349894053/20000000000000 : ℝ)^7 := by
    have hnat : (4700155687 : ℕ)^9*20000000000000^7 ≤ 7576349894053^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4700155687 10000000000 7576349894053 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1636223807/2500000000 : ℝ)^9 ≤ (57983372232377/100000000000000 : ℝ)^7 := by
    have hnat : (1636223807 : ℕ)^9*100000000000000^7 ≤ 57983372232377^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636223807 2500000000 57983372232377 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-839296587/10000000000 : ℝ), (4700155687/10000000000 : ℝ), (-1636223807/2500000000 : ℝ)] ![(2067439144379/50000000000000 : ℝ), (7576349894053/20000000000000 : ℝ), (57983372232377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-839296587/10000000000 : ℝ)|^9 ≤ (2067439144379/50000000000000 : ℝ)^7
        have hw : |(-839296587/10000000000 : ℝ)|=(839296587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4700155687/10000000000 : ℝ)|^9 ≤ (7576349894053/20000000000000 : ℝ)^7
        have hw : |(4700155687/10000000000 : ℝ)|=(4700155687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1636223807/2500000000 : ℝ)|^9 ≤ (57983372232377/100000000000000 : ℝ)^7
        have hw : |(-1636223807/2500000000 : ℝ)|=(1636223807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4439027667/10000000000 : ℝ)*x 0 + (-1390107799/10000000000 : ℝ)*x 1 + (-3224434731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4439027667/10000000000 : ℝ)^9 ≤ (35197591968027/100000000000000 : ℝ)^7 := by
    have hnat : (4439027667 : ℕ)^9*100000000000000^7 ≤ 35197591968027^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439027667 10000000000 35197591968027 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1390107799/10000000000 : ℝ)^9 ≤ (7910522833101/100000000000000 : ℝ)^7 := by
    have hnat : (1390107799 : ℕ)^9*100000000000000^7 ≤ 7910522833101^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390107799 10000000000 7910522833101 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3224434731/5000000000 : ℝ)^9 ≤ (56891885185023/100000000000000 : ℝ)^7 := by
    have hnat : (3224434731 : ℕ)^9*100000000000000^7 ≤ 56891885185023^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3224434731 5000000000 56891885185023 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4439027667/10000000000 : ℝ), (-1390107799/10000000000 : ℝ), (-3224434731/5000000000 : ℝ)] ![(35197591968027/100000000000000 : ℝ), (7910522833101/100000000000000 : ℝ), (56891885185023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4439027667/10000000000 : ℝ)|^9 ≤ (35197591968027/100000000000000 : ℝ)^7
        have hw : |(4439027667/10000000000 : ℝ)|=(4439027667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1390107799/10000000000 : ℝ)|^9 ≤ (7910522833101/100000000000000 : ℝ)^7
        have hw : |(-1390107799/10000000000 : ℝ)|=(1390107799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3224434731/5000000000 : ℝ)|^9 ≤ (56891885185023/100000000000000 : ℝ)^7
        have hw : |(-3224434731/5000000000 : ℝ)|=(3224434731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6145458523/10000000000 : ℝ)*x 0 + (4951443949/10000000000 : ℝ)*x 1 + (1124200109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6145458523/10000000000 : ℝ)^9 ≤ (10694764556059/20000000000000 : ℝ)^7 := by
    have hnat : (6145458523 : ℕ)^9*20000000000000^7 ≤ 10694764556059^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6145458523 10000000000 10694764556059 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4951443949/10000000000 : ℝ)^9 ≤ (2025267553263/5000000000000 : ℝ)^7 := by
    have hnat : (4951443949 : ℕ)^9*5000000000000^7 ≤ 2025267553263^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4951443949 10000000000 2025267553263 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124200109/10000000000 : ℝ)^9 ≤ (3010413071987/50000000000000 : ℝ)^7 := by
    have hnat : (1124200109 : ℕ)^9*50000000000000^7 ≤ 3010413071987^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124200109 10000000000 3010413071987 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6145458523/10000000000 : ℝ), (4951443949/10000000000 : ℝ), (1124200109/10000000000 : ℝ)] ![(10694764556059/20000000000000 : ℝ), (2025267553263/5000000000000 : ℝ), (3010413071987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6145458523/10000000000 : ℝ)|^9 ≤ (10694764556059/20000000000000 : ℝ)^7
        have hw : |(6145458523/10000000000 : ℝ)|=(6145458523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4951443949/10000000000 : ℝ)|^9 ≤ (2025267553263/5000000000000 : ℝ)^7
        have hw : |(4951443949/10000000000 : ℝ)|=(4951443949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124200109/10000000000 : ℝ)|^9 ≤ (3010413071987/50000000000000 : ℝ)^7
        have hw : |(1124200109/10000000000 : ℝ)|=(1124200109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3371930993/5000000000 : ℝ)*x 0 + (925990149/2000000000 : ℝ)*x 1 + (-582381827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3371930993/5000000000 : ℝ)^9 ≤ (15064872014937/25000000000000 : ℝ)^7 := by
    have hnat : (3371930993 : ℕ)^9*25000000000000^7 ≤ 15064872014937^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3371930993 5000000000 15064872014937 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925990149/2000000000 : ℝ)^9 ≤ (37155812493287/100000000000000 : ℝ)^7 := by
    have hnat : (925990149 : ℕ)^9*100000000000000^7 ≤ 37155812493287^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925990149 2000000000 37155812493287 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (582381827/10000000000 : ℝ)^9 ≤ (10096482153/390625000000 : ℝ)^7 := by
    have hnat : (582381827 : ℕ)^9*390625000000^7 ≤ 10096482153^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582381827 10000000000 10096482153 390625000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3371930993/5000000000 : ℝ), (925990149/2000000000 : ℝ), (-582381827/10000000000 : ℝ)] ![(15064872014937/25000000000000 : ℝ), (37155812493287/100000000000000 : ℝ), (10096482153/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3371930993/5000000000 : ℝ)|^9 ≤ (15064872014937/25000000000000 : ℝ)^7
        have hw : |(3371930993/5000000000 : ℝ)|=(3371930993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(925990149/2000000000 : ℝ)|^9 ≤ (37155812493287/100000000000000 : ℝ)^7
        have hw : |(925990149/2000000000 : ℝ)|=(925990149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-582381827/10000000000 : ℝ)|^9 ≤ (10096482153/390625000000 : ℝ)^7
        have hw : |(-582381827/10000000000 : ℝ)|=(582381827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-285559467/5000000000 : ℝ)*x 0 + (2751404703/5000000000 : ℝ)*x 1 + (-5930849351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (285559467/5000000000 : ℝ)^9 ≤ (630152384073/25000000000000 : ℝ)^7 := by
    have hnat : (285559467 : ℕ)^9*25000000000000^7 ≤ 630152384073^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285559467 5000000000 630152384073 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751404703/5000000000 : ℝ)^9 ≤ (46394419851173/100000000000000 : ℝ)^7 := by
    have hnat : (2751404703 : ℕ)^9*100000000000000^7 ≤ 46394419851173^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751404703 5000000000 46394419851173 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5930849351/10000000000 : ℝ)^9 ≤ (12771242649317/25000000000000 : ℝ)^7 := by
    have hnat : (5930849351 : ℕ)^9*25000000000000^7 ≤ 12771242649317^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5930849351 10000000000 12771242649317 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-285559467/5000000000 : ℝ), (2751404703/5000000000 : ℝ), (-5930849351/10000000000 : ℝ)] ![(630152384073/25000000000000 : ℝ), (46394419851173/100000000000000 : ℝ), (12771242649317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-285559467/5000000000 : ℝ)|^9 ≤ (630152384073/25000000000000 : ℝ)^7
        have hw : |(-285559467/5000000000 : ℝ)|=(285559467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751404703/5000000000 : ℝ)|^9 ≤ (46394419851173/100000000000000 : ℝ)^7
        have hw : |(2751404703/5000000000 : ℝ)|=(2751404703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5930849351/10000000000 : ℝ)|^9 ≤ (12771242649317/25000000000000 : ℝ)^7
        have hw : |(-5930849351/10000000000 : ℝ)|=(5930849351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1543349589/2500000000 : ℝ)*x 0 + (-1240659419/10000000000 : ℝ)*x 1 + (-968805107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1543349589/2500000000 : ℝ)^9 ≤ (53786601277793/100000000000000 : ℝ)^7 := by
    have hnat : (1543349589 : ℕ)^9*100000000000000^7 ≤ 53786601277793^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543349589 2500000000 53786601277793 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1240659419/10000000000 : ℝ)^9 ≤ (3417166772789/50000000000000 : ℝ)^7 := by
    have hnat : (1240659419 : ℕ)^9*50000000000000^7 ≤ 3417166772789^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240659419 10000000000 3417166772789 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968805107/2000000000 : ℝ)^9 ≤ (19689532584117/50000000000000 : ℝ)^7 := by
    have hnat : (968805107 : ℕ)^9*50000000000000^7 ≤ 19689532584117^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968805107 2000000000 19689532584117 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1543349589/2500000000 : ℝ), (-1240659419/10000000000 : ℝ), (-968805107/2000000000 : ℝ)] ![(53786601277793/100000000000000 : ℝ), (3417166772789/50000000000000 : ℝ), (19689532584117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1543349589/2500000000 : ℝ)|^9 ≤ (53786601277793/100000000000000 : ℝ)^7
        have hw : |(1543349589/2500000000 : ℝ)|=(1543349589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1240659419/10000000000 : ℝ)|^9 ≤ (3417166772789/50000000000000 : ℝ)^7
        have hw : |(-1240659419/10000000000 : ℝ)|=(1240659419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-968805107/2000000000 : ℝ)|^9 ≤ (19689532584117/50000000000000 : ℝ)^7
        have hw : |(-968805107/2000000000 : ℝ)|=(968805107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4584644337/10000000000 : ℝ)*x 0 + (5754097243/10000000000 : ℝ)*x 1 + (2188139703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4584644337/10000000000 : ℝ)^9 ≤ (18344498354357/50000000000000 : ℝ)^7 := by
    have hnat : (4584644337 : ℕ)^9*50000000000000^7 ≤ 18344498354357^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584644337 10000000000 18344498354357 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5754097243/10000000000 : ℝ)^9 ≤ (6141992282657/12500000000000 : ℝ)^7 := by
    have hnat : (5754097243 : ℕ)^9*12500000000000^7 ≤ 6141992282657^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5754097243 10000000000 6141992282657 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188139703/10000000000 : ℝ)^9 ≤ (7087532508489/50000000000000 : ℝ)^7 := by
    have hnat : (2188139703 : ℕ)^9*50000000000000^7 ≤ 7087532508489^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188139703 10000000000 7087532508489 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4584644337/10000000000 : ℝ), (5754097243/10000000000 : ℝ), (2188139703/10000000000 : ℝ)] ![(18344498354357/50000000000000 : ℝ), (6141992282657/12500000000000 : ℝ), (7087532508489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4584644337/10000000000 : ℝ)|^9 ≤ (18344498354357/50000000000000 : ℝ)^7
        have hw : |(4584644337/10000000000 : ℝ)|=(4584644337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5754097243/10000000000 : ℝ)|^9 ≤ (6141992282657/12500000000000 : ℝ)^7
        have hw : |(5754097243/10000000000 : ℝ)|=(5754097243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2188139703/10000000000 : ℝ)|^9 ≤ (7087532508489/50000000000000 : ℝ)^7
        have hw : |(2188139703/10000000000 : ℝ)|=(2188139703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311062_s2_s2_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3480130269/5000000000 : ℝ)*x 0 + (4288166297/10000000000 : ℝ)*x 1 + (-187413853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3480130269/5000000000 : ℝ)^9 ≤ (6275688122211/10000000000000 : ℝ)^7 := by
    have hnat : (3480130269 : ℕ)^9*10000000000000^7 ≤ 6275688122211^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3480130269 5000000000 6275688122211 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4288166297/10000000000 : ℝ)^9 ≤ (16833575524547/50000000000000 : ℝ)^7 := by
    have hnat : (4288166297 : ℕ)^9*50000000000000^7 ≤ 16833575524547^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288166297 10000000000 16833575524547 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187413853/2500000000 : ℝ)^9 ≤ (893991929197/25000000000000 : ℝ)^7 := by
    have hnat : (187413853 : ℕ)^9*25000000000000^7 ≤ 893991929197^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187413853 2500000000 893991929197 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3480130269/5000000000 : ℝ), (4288166297/10000000000 : ℝ), (-187413853/2500000000 : ℝ)] ![(6275688122211/10000000000000 : ℝ), (16833575524547/50000000000000 : ℝ), (893991929197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3480130269/5000000000 : ℝ)|^9 ≤ (6275688122211/10000000000000 : ℝ)^7
        have hw : |(3480130269/5000000000 : ℝ)|=(3480130269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4288166297/10000000000 : ℝ)|^9 ≤ (16833575524547/50000000000000 : ℝ)^7
        have hw : |(4288166297/10000000000 : ℝ)|=(4288166297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187413853/2500000000 : ℝ)|^9 ≤ (893991929197/25000000000000 : ℝ)^7
        have hw : |(-187413853/2500000000 : ℝ)|=(187413853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311062_s2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((70071/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70071/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35009/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35009/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13741/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13741/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11051/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11051/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5569/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5569/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1183/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1183/4000 : ℝ)*X 1 2) := by
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
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (70071/100000 : ℝ) ^ (71/16 : ℝ) ≤ (20633660230675039451/100000000000000000000 : ℝ) := by
    have hpowers : (70071/100000 : ℝ)^71 ≤ (20633660230675039451/100000000000000000000 : ℝ)^16 := by
      have hnat : (70071 : ℕ)^71*100000000000000000000^16 ≤ 20633660230675039451^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70071 100000 20633660230675039451 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70071/100000 : ℝ)) (X := (20633660230675039451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (120633660230675039451/100000000000000000000 : ℝ) ≤ (1303974542615199/1250000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (120633660230675039451/100000000000000000000 : ℝ)^16 ≤ (1303974542615199/1250000000000000 : ℝ)^71 := by
      have hnat : (120633660230675039451 : ℕ)^16*1250000000000000^71 ≤ 1303974542615199^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120633660230675039451 100000000000000000000 1303974542615199 1250000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1303974542615199/1250000000000000 : ℝ)) (X := (120633660230675039451/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (70633660230675039451/50000000000000000000 : ℝ) ≤ (5404832260593377/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (70633660230675039451/50000000000000000000 : ℝ)^16 ≤ (5404832260593377/5000000000000000 : ℝ)^71 := by
      have hnat : (70633660230675039451 : ℕ)^16*5000000000000000^71 ≤ 5404832260593377^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70633660230675039451 50000000000000000000 5404832260593377 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5404832260593377/5000000000000000 : ℝ)) (X := (70633660230675039451/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(53974542615199/875887500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188934090132581/3503550000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (70071/100000 : ℝ)) (alpha := (53974542615199/875887500000000 : ℝ)) (beta := (188934090132581/3503550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (70071/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(53974542615199/875887500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188934090132581/3503550000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (35009/50000 : ℝ) ^ (71/16 : ℝ) ≤ (10282247519624417333/50000000000000000000 : ℝ) := by
    have hpowers : (35009/50000 : ℝ)^71 ≤ (10282247519624417333/50000000000000000000 : ℝ)^16 := by
      have hnat : (35009 : ℕ)^71*50000000000000000000^16 ≤ 10282247519624417333^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35009 50000 10282247519624417333 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35009/50000 : ℝ)) (X := (10282247519624417333/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (60282247519624417333/50000000000000000000 : ℝ) ≤ (10430448196936843/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (60282247519624417333/50000000000000000000 : ℝ)^16 ≤ (10430448196936843/10000000000000000 : ℝ)^71 := by
      have hnat : (60282247519624417333 : ℕ)^16*10000000000000000^71 ≤ 10430448196936843^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60282247519624417333 50000000000000000000 10430448196936843 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10430448196936843/10000000000000000 : ℝ)) (X := (60282247519624417333/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (35282247519624417333/25000000000000000000 : ℝ) ≤ (2701819569775563/2500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (35282247519624417333/25000000000000000000 : ℝ)^16 ≤ (2701819569775563/2500000000000000 : ℝ)^71 := by
      have hnat : (35282247519624417333 : ℕ)^16*2500000000000000^71 ≤ 2701819569775563^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35282247519624417333 25000000000000000000 2701819569775563 2500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2701819569775563/2500000000000000 : ℝ)) (X := (35282247519624417333/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(430448196936843/7001800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(376830082165409/7001800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (35009/50000 : ℝ)) (alpha := (430448196936843/7001800000000000 : ℝ)) (beta := (376830082165409/7001800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (35009/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(430448196936843/7001800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(376830082165409/7001800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (13741/25000 : ℝ) ^ (71/16 : ℝ) ≤ (3512105861543226977/50000000000000000000 : ℝ) := by
    have hpowers : (13741/25000 : ℝ)^71 ≤ (3512105861543226977/50000000000000000000 : ℝ)^16 := by
      have hnat : (13741 : ℕ)^71*50000000000000000000^16 ≤ 3512105861543226977^16*25000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13741 25000 3512105861543226977 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13741/25000 : ℝ)) (X := (3512105861543226977/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (53512105861543226977/50000000000000000000 : ℝ) ≤ (10154156192587997/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (53512105861543226977/50000000000000000000 : ℝ)^16 ≤ (10154156192587997/10000000000000000 : ℝ)^71 := by
      have hnat : (53512105861543226977 : ℕ)^16*10000000000000000^71 ≤ 10154156192587997^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53512105861543226977 50000000000000000000 10154156192587997 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10154156192587997/10000000000000000 : ℝ)) (X := (53512105861543226977/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (28512105861543226977/25000000000000000000 : ℝ) ≤ (10300663293409337/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (28512105861543226977/25000000000000000000 : ℝ)^16 ≤ (10300663293409337/10000000000000000 : ℝ)^71 := by
      have hnat : (28512105861543226977 : ℕ)^16*10000000000000000^71 ≤ 10300663293409337^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28512105861543226977 25000000000000000000 10300663293409337 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10300663293409337/10000000000000000 : ℝ)) (X := (28512105861543226977/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(154156192587997/5496400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1046479291581/39260000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (13741/25000 : ℝ)) (alpha := (154156192587997/5496400000000000 : ℝ)) (beta := (1046479291581/39260000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13741/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(154156192587997/5496400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1046479291581/39260000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-70124347/400000000 : ℝ)*X 0 0+(192463/390625 : ℝ)*X 0 1+(-1437502821/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((4931955169/10000000000 : ℝ)*X 1 0+(-878485547/5000000000 : ℝ)*X 1 1+(-5742566777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1292518991/2500000000 : ℝ)*X 2 0+(5176125251/10000000000 : ℝ)*X 2 1+(1101388987/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-667298711/5000000000 : ℝ)*X 0 0+(2182314739/5000000000 : ℝ)*X 0 1+(-655094757/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((118860761/250000000 : ℝ)*X 1 0+(-447973223/5000000000 : ℝ)*X 1 1+(-1615872877/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2385561911/5000000000 : ℝ)*X 2 0+(316117809/500000000 : ℝ)*X 2 1+(1109577611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((503471383/1000000000 : ℝ)*X 0 0+(1275979119/2000000000 : ℝ)*X 0 1+(-568541571/10000000000 : ℝ)*X 0 2+(503471383/1000000000 : ℝ)*X 1 0+(1275979119/2000000000 : ℝ)*X 1 1+(-568541571/10000000000 : ℝ)*X 1 2+(503471383/1000000000 : ℝ)*X 2 0+(1275979119/2000000000 : ℝ)*X 2 1+(-568541571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-839296587/10000000000 : ℝ)*X 0 0+(4700155687/10000000000 : ℝ)*X 0 1+(-1636223807/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4439027667/10000000000 : ℝ)*X 1 0+(-1390107799/10000000000 : ℝ)*X 1 1+(-3224434731/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6145458523/10000000000 : ℝ)*X 2 0+(4951443949/10000000000 : ℝ)*X 2 1+(1124200109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3371930993/5000000000 : ℝ)*X 0 0+(925990149/2000000000 : ℝ)*X 0 1+(-582381827/10000000000 : ℝ)*X 0 2+(3371930993/5000000000 : ℝ)*X 1 0+(925990149/2000000000 : ℝ)*X 1 1+(-582381827/10000000000 : ℝ)*X 1 2+(3371930993/5000000000 : ℝ)*X 2 0+(925990149/2000000000 : ℝ)*X 2 1+(-582381827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-285559467/5000000000 : ℝ)*X 0 0+(2751404703/5000000000 : ℝ)*X 0 1+(-5930849351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1543349589/2500000000 : ℝ)*X 1 0+(-1240659419/10000000000 : ℝ)*X 1 1+(-968805107/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4584644337/10000000000 : ℝ)*X 2 0+(5754097243/10000000000 : ℝ)*X 2 1+(2188139703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3480130269/5000000000 : ℝ)*X 0 0+(4288166297/10000000000 : ℝ)*X 0 1+(-187413853/2500000000 : ℝ)*X 0 2+(3480130269/5000000000 : ℝ)*X 1 0+(4288166297/10000000000 : ℝ)*X 1 1+(-187413853/2500000000 : ℝ)*X 1 2+(3480130269/5000000000 : ℝ)*X 2 0+(4288166297/10000000000 : ℝ)*X 2 1+(-187413853/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((11051/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11051/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (608527782318550186230754767/64189707400000000000000000000000 : ℝ) := by norm_num
    linear_combination (11691627299/200000000000 : ℝ)*(base39) + (7280551/1000000000000 : ℝ)*(base49) + (18843610321/125000000000 : ℝ)*(base60) + (4846178041763/1000000000000 : ℝ)*(major_s2_0) + (4846178041763/1000000000000 : ℝ)*(major_s2_1) + (4846178041763/1000000000000 : ℝ)*(major_s2_2) + (4435627/62500000000 : ℝ)*(sp_s2_0) + (1348709688683/200000000000 : ℝ)*(sp_s2_7) + (6743519729109/1000000000000 : ℝ)*(sp_s2_8) + (674353545697/100000000000 : ℝ)*(sp_s2_9) + (589745910113/200000000000 : ℝ)*(sp_s2_13) + (3959459/1000000000000 : ℝ)*(sp_s2_14) + (103643797/1000000000000 : ℝ)*(sp_s2_15) + (87915937/1000000000000 : ℝ)*(sp_s2_23) + (589745910113/200000000000 : ℝ)*(f.failure) + (3371811686453/500000000000 : ℝ)*(f.sum) + (8166646286503537309/14801805200000000000000000000000 : ℝ)*base63 + (445197059413/1570400000000000000000000 : ℝ)*base64 + (1594000524018967/7001800000000000000000000000 : ℝ)*base67 + (2586318581031951/5496400000000000000000000000 : ℝ)*base69 + (2375106120629220527/13754937300000000000000000000000 : ℝ)*base70 + (542908407446671/1751775000000000000000000000 : ℝ)*base72 + (2899289847296411/7001800000000000000000000000 : ℝ)*base74 + (759751698238541/1751775000000000000000000000 : ℝ)*base76 + (37403173809360069563/98124625560000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (2169/5000000000000000 : ℝ)*base86 + (2169/5000000000000000 : ℝ)*base88 + (2169/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5569/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5569/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (365903623009404838588213759663/24694697432600000000000000000000000 : ℝ) := by norm_num
    linear_combination (64966516197/1000000000000 : ℝ)*(base39) + (1502427/500000000000 : ℝ)*(base60) + (4901351407267/1000000000000 : ℝ)*(major_s2_0) + (4901351407267/1000000000000 : ℝ)*(major_s2_1) + (4901351407267/1000000000000 : ℝ)*(major_s2_2) + (2874247/1000000000000 : ℝ)*(sp_s2_0) + (13965499/500000000000 : ℝ)*(sp_s2_2) + (17108749/250000000000 : ℝ)*(sp_s2_7) + (9937401/200000000000 : ℝ)*(sp_s2_8) + (1705081488951/250000000000 : ℝ)*(sp_s2_14) + (6820347578041/1000000000000 : ℝ)*(sp_s2_15) + (213136541689/31250000000 : ℝ)*(sp_s2_16) + (745525858717/250000000000 : ℝ)*(sp_s2_20) + (39435117/200000000000 : ℝ)*(sp_s2_27) + (2982300610453/1000000000000 : ℝ)*(f.failure) + (3410198632523/500000000000 : ℝ)*(f.sum) + (404657011215055317/2114543600000000000000000000000 : ℝ)*base62 + (15132527208239/39260000000000000000000000 : ℝ)*base64 + (5195877718513683/7001800000000000000000000000 : ℝ)*base67 + (346416744761543/785200000000000000000000000 : ℝ)*base68 + (3032550542021071037/13754937300000000000000000000000 : ℝ)*base71 + (994560339221117/3503550000000000000000000000 : ℝ)*base73 + (1101858586397639/7001800000000000000000000000 : ℝ)*base74 + (709009878461993/3503550000000000000000000000 : ℝ)*base76 + (15018789831214082429/98124625560000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (7411/25000000000000000 : ℝ)*base87 + (7411/25000000000000000 : ℝ)*base89 + (7411/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1183/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1183/4000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2571023699765713990587335528179/172862882028200000000000000000000000 : ℝ) := by norm_num
    linear_combination (11806391/1000000000000 : ℝ)*(base11) + (118758272179/200000000000 : ℝ)*(base39) + (253323/500000000000 : ℝ)*(base59) + (3929120620273/1000000000000 : ℝ)*(major_s2_0) + (3929120620273/1000000000000 : ℝ)*(major_s2_1) + (3929120620273/1000000000000 : ℝ)*(major_s2_2) + (36165049/1000000000000 : ℝ)*(sp_s2_0) + (85021/40000000000 : ℝ)*(sp_s2_1) + (8633699/500000000000 : ℝ)*(sp_s2_2) + (67906371/1000000000000 : ℝ)*(sp_s2_9) + (2733728036147/500000000000 : ℝ)*(sp_s2_21) + (5467501918209/1000000000000 : ℝ)*(sp_s2_22) + (1093483773993/200000000000 : ℝ)*(sp_s2_23) + (1195366119537/500000000000 : ℝ)*(sp_s2_27) + (1195366119537/500000000000 : ℝ)*(f.failure) + (1093500808747/200000000000 : ℝ)*(f.sum) + (886879637442001041/14801805200000000000000000000000 : ℝ)*base62 + (7326158095721/39260000000000000000000000 : ℝ)*base65 + (714394008604297/7001800000000000000000000000 : ℝ)*base67 + (237176497508059/5496400000000000000000000000 : ℝ)*base68 + (400801078445411213/13754937300000000000000000000000 : ℝ)*base71 + (1184927888185553/3503550000000000000000000000 : ℝ)*base73 + (560155851779041/7001800000000000000000000000 : ℝ)*base74 + (250461515261297/3503550000000000000000000000 : ℝ)*base76 + (40815863308554326303/98124625560000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (4219/12500000000000000 : ℝ)*base87 + (4219/12500000000000000 : ℝ)*base89 + (4219/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((70071/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70071/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35009/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35009/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13741/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13741/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11051/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11051/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5569/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5569/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1183/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1183/4000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311062_s2 p hpa hpb X hX hprev1

#print axioms solution

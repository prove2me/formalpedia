-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b037
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:42:06.275311+00:00
-- url     : https://prove2.me/submissions/d89a74a9-80d1-4fdb-901f-8199fcca0399

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301080
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
theorem collision_support_c301079_s0_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (127801487/156250000 : ℝ)*x 0 + (-1542451073/10000000000 : ℝ)*x 1 + (-2395706983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127801487/156250000 : ℝ)^65 ≤ (76597561522509/100000000000000 : ℝ)^49 := by
    have hnat : (127801487 : ℕ)^65*100000000000000^49 ≤ 76597561522509^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127801487 156250000 76597561522509 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1542451073/10000000000 : ℝ)^65 ≤ (4188973102481/50000000000000 : ℝ)^49 := by
    have hnat : (1542451073 : ℕ)^65*50000000000000^49 ≤ 4188973102481^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542451073 10000000000 4188973102481 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395706983/10000000000 : ℝ)^65 ≤ (7512246132827/50000000000000 : ℝ)^49 := by
    have hnat : (2395706983 : ℕ)^65*50000000000000^49 ≤ 7512246132827^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395706983 10000000000 7512246132827 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127801487/156250000 : ℝ), (-1542451073/10000000000 : ℝ), (-2395706983/10000000000 : ℝ)] ![(76597561522509/100000000000000 : ℝ), (4188973102481/50000000000000 : ℝ), (7512246132827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127801487/156250000 : ℝ)|^65 ≤ (76597561522509/100000000000000 : ℝ)^49
        have hw : |(127801487/156250000 : ℝ)|=(127801487/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1542451073/10000000000 : ℝ)|^65 ≤ (4188973102481/50000000000000 : ℝ)^49
        have hw : |(-1542451073/10000000000 : ℝ)|=(1542451073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2395706983/10000000000 : ℝ)|^65 ≤ (7512246132827/50000000000000 : ℝ)^49
        have hw : |(-2395706983/10000000000 : ℝ)|=(2395706983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (819688979/2500000000 : ℝ)*x 0 + (3040146939/5000000000 : ℝ)*x 1 + (3573149269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819688979/2500000000 : ℝ)^65 ≤ (5695256490119/25000000000000 : ℝ)^49 := by
    have hnat : (819688979 : ℕ)^65*25000000000000^49 ≤ 5695256490119^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819688979 2500000000 5695256490119 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3040146939/5000000000 : ℝ)^65 ≤ (51685572147973/100000000000000 : ℝ)^49 := by
    have hnat : (3040146939 : ℕ)^65*100000000000000^49 ≤ 51685572147973^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3040146939 5000000000 51685572147973 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3573149269/10000000000 : ℝ)^65 ≤ (12766700937371/50000000000000 : ℝ)^49 := by
    have hnat : (3573149269 : ℕ)^65*50000000000000^49 ≤ 12766700937371^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3573149269 10000000000 12766700937371 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(819688979/2500000000 : ℝ), (3040146939/5000000000 : ℝ), (3573149269/10000000000 : ℝ)] ![(5695256490119/25000000000000 : ℝ), (51685572147973/100000000000000 : ℝ), (12766700937371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(819688979/2500000000 : ℝ)|^65 ≤ (5695256490119/25000000000000 : ℝ)^49
        have hw : |(819688979/2500000000 : ℝ)|=(819688979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3040146939/5000000000 : ℝ)|^65 ≤ (51685572147973/100000000000000 : ℝ)^49
        have hw : |(3040146939/5000000000 : ℝ)|=(3040146939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3573149269/10000000000 : ℝ)|^65 ≤ (12766700937371/50000000000000 : ℝ)^49
        have hw : |(3573149269/10000000000 : ℝ)|=(3573149269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1756788659/5000000000 : ℝ)*x 0 + (1065213007/2000000000 : ℝ)*x 1 + (-840645727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1756788659/5000000000 : ℝ)^65 ≤ (12485123140553/50000000000000 : ℝ)^49 := by
    have hnat : (1756788659 : ℕ)^65*50000000000000^49 ≤ 12485123140553^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756788659 5000000000 12485123140553 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065213007/2000000000 : ℝ)^65 ≤ (4335805587887/10000000000000 : ℝ)^49 := by
    have hnat : (1065213007 : ℕ)^65*10000000000000^49 ≤ 4335805587887^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065213007 2000000000 4335805587887 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (840645727/2000000000 : ℝ)^65 ≤ (494870278581/1562500000000 : ℝ)^49 := by
    have hnat : (840645727 : ℕ)^65*1562500000000^49 ≤ 494870278581^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840645727 2000000000 494870278581 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1756788659/5000000000 : ℝ), (1065213007/2000000000 : ℝ), (-840645727/2000000000 : ℝ)] ![(12485123140553/50000000000000 : ℝ), (4335805587887/10000000000000 : ℝ), (494870278581/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1756788659/5000000000 : ℝ)|^65 ≤ (12485123140553/50000000000000 : ℝ)^49
        have hw : |(1756788659/5000000000 : ℝ)|=(1756788659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1065213007/2000000000 : ℝ)|^65 ≤ (4335805587887/10000000000000 : ℝ)^49
        have hw : |(1065213007/2000000000 : ℝ)|=(1065213007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-840645727/2000000000 : ℝ)|^65 ≤ (494870278581/1562500000000 : ℝ)^49
        have hw : |(-840645727/2000000000 : ℝ)|=(840645727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-833787213/5000000000 : ℝ)*x 0 + (2888118931/10000000000 : ℝ)*x 1 + (-7761908371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833787213/5000000000 : ℝ)^65 ≤ (1858241840183/20000000000000 : ℝ)^49 := by
    have hnat : (833787213 : ℕ)^65*20000000000000^49 ≤ 1858241840183^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833787213 5000000000 1858241840183 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2888118931/10000000000 : ℝ)^65 ≤ (3850519956067/20000000000000 : ℝ)^49 := by
    have hnat : (2888118931 : ℕ)^65*20000000000000^49 ≤ 3850519956067^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2888118931 10000000000 3850519956067 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7761908371/10000000000 : ℝ)^65 ≤ (71456191014377/100000000000000 : ℝ)^49 := by
    have hnat : (7761908371 : ℕ)^65*100000000000000^49 ≤ 71456191014377^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7761908371 10000000000 71456191014377 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-833787213/5000000000 : ℝ), (2888118931/10000000000 : ℝ), (-7761908371/10000000000 : ℝ)] ![(1858241840183/20000000000000 : ℝ), (3850519956067/20000000000000 : ℝ), (71456191014377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-833787213/5000000000 : ℝ)|^65 ≤ (1858241840183/20000000000000 : ℝ)^49
        have hw : |(-833787213/5000000000 : ℝ)|=(833787213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2888118931/10000000000 : ℝ)|^65 ≤ (3850519956067/20000000000000 : ℝ)^49
        have hw : |(2888118931/10000000000 : ℝ)|=(2888118931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7761908371/10000000000 : ℝ)|^65 ≤ (71456191014377/100000000000000 : ℝ)^49
        have hw : |(-7761908371/10000000000 : ℝ)|=(7761908371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8072261987/10000000000 : ℝ)*x 0 + (-520143/19531250 : ℝ)*x 1 + (-136038093/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8072261987/10000000000 : ℝ)^65 ≤ (75270768506147/100000000000000 : ℝ)^49 := by
    have hnat : (8072261987 : ℕ)^65*100000000000000^49 ≤ 75270768506147^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8072261987 10000000000 75270768506147 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520143/19531250 : ℝ)^65 ≤ (815145695853/100000000000000 : ℝ)^49 := by
    have hnat : (520143 : ℕ)^65*100000000000000^49 ≤ 815145695853^49*19531250^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520143 19531250 815145695853 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136038093/400000000 : ℝ)^65 ≤ (23914085785451/100000000000000 : ℝ)^49 := by
    have hnat : (136038093 : ℕ)^65*100000000000000^49 ≤ 23914085785451^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136038093 400000000 23914085785451 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8072261987/10000000000 : ℝ), (-520143/19531250 : ℝ), (-136038093/400000000 : ℝ)] ![(75270768506147/100000000000000 : ℝ), (815145695853/100000000000000 : ℝ), (23914085785451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8072261987/10000000000 : ℝ)|^65 ≤ (75270768506147/100000000000000 : ℝ)^49
        have hw : |(8072261987/10000000000 : ℝ)|=(8072261987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520143/19531250 : ℝ)|^65 ≤ (815145695853/100000000000000 : ℝ)^49
        have hw : |(-520143/19531250 : ℝ)|=(520143/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136038093/400000000 : ℝ)|^65 ≤ (23914085785451/100000000000000 : ℝ)^49
        have hw : |(-136038093/400000000 : ℝ)|=(136038093/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (278244079/2000000000 : ℝ)*x 0 + (8032811997/10000000000 : ℝ)*x 1 + (2735024053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (278244079/2000000000 : ℝ)^65 ≤ (7306148348447/100000000000000 : ℝ)^49 := by
    have hnat : (278244079 : ℕ)^65*100000000000000^49 ≤ 7306148348447^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278244079 2000000000 7306148348447 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8032811997/10000000000 : ℝ)^65 ≤ (3739159293289/5000000000000 : ℝ)^49 := by
    have hnat : (8032811997 : ℕ)^65*5000000000000^49 ≤ 3739159293289^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8032811997 10000000000 3739159293289 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735024053/10000000000 : ℝ)^65 ≤ (3582133154483/20000000000000 : ℝ)^49 := by
    have hnat : (2735024053 : ℕ)^65*20000000000000^49 ≤ 3582133154483^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735024053 10000000000 3582133154483 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(278244079/2000000000 : ℝ), (8032811997/10000000000 : ℝ), (2735024053/10000000000 : ℝ)] ![(7306148348447/100000000000000 : ℝ), (3739159293289/5000000000000 : ℝ), (3582133154483/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(278244079/2000000000 : ℝ)|^65 ≤ (7306148348447/100000000000000 : ℝ)^49
        have hw : |(278244079/2000000000 : ℝ)|=(278244079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8032811997/10000000000 : ℝ)|^65 ≤ (3739159293289/5000000000000 : ℝ)^49
        have hw : |(8032811997/10000000000 : ℝ)|=(8032811997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735024053/10000000000 : ℝ)|^65 ≤ (3582133154483/20000000000000 : ℝ)^49
        have hw : |(2735024053/10000000000 : ℝ)|=(2735024053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (94877731/400000000 : ℝ)*x 0 + (7674805877/10000000000 : ℝ)*x 1 + (-147879401/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94877731/400000000 : ℝ)^65 ≤ (3706779319607/25000000000000 : ℝ)^49 := by
    have hnat : (94877731 : ℕ)^65*25000000000000^49 ≤ 3706779319607^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94877731 400000000 3706779319607 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7674805877/10000000000 : ℝ)^65 ≤ (35197222319777/50000000000000 : ℝ)^49 := by
    have hnat : (7674805877 : ℕ)^65*50000000000000^49 ≤ 35197222319777^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7674805877 10000000000 35197222319777 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147879401/625000000 : ℝ)^65 ≤ (14778438061611/100000000000000 : ℝ)^49 := by
    have hnat : (147879401 : ℕ)^65*100000000000000^49 ≤ 14778438061611^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147879401 625000000 14778438061611 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(94877731/400000000 : ℝ), (7674805877/10000000000 : ℝ), (-147879401/625000000 : ℝ)] ![(3706779319607/25000000000000 : ℝ), (35197222319777/50000000000000 : ℝ), (14778438061611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(94877731/400000000 : ℝ)|^65 ≤ (3706779319607/25000000000000 : ℝ)^49
        have hw : |(94877731/400000000 : ℝ)|=(94877731/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7674805877/10000000000 : ℝ)|^65 ≤ (35197222319777/50000000000000 : ℝ)^49
        have hw : |(7674805877/10000000000 : ℝ)|=(7674805877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147879401/625000000 : ℝ)|^65 ≤ (14778438061611/100000000000000 : ℝ)^49
        have hw : |(-147879401/625000000 : ℝ)|=(147879401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-282582427/10000000000 : ℝ)*x 0 + (1786866083/5000000000 : ℝ)*x 1 + (-3967563653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (282582427/10000000000 : ℝ)^65 ≤ (55115867317/6250000000000 : ℝ)^49 := by
    have hnat : (282582427 : ℕ)^65*6250000000000^49 ≤ 55115867317^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282582427 10000000000 55115867317 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1786866083/5000000000 : ℝ)^65 ≤ (2553892745873/10000000000000 : ℝ)^49 := by
    have hnat : (1786866083 : ℕ)^65*10000000000000^49 ≤ 2553892745873^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786866083 5000000000 2553892745873 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3967563653/5000000000 : ℝ)^65 ≤ (73579218658363/100000000000000 : ℝ)^49 := by
    have hnat : (3967563653 : ℕ)^65*100000000000000^49 ≤ 73579218658363^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3967563653 5000000000 73579218658363 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-282582427/10000000000 : ℝ), (1786866083/5000000000 : ℝ), (-3967563653/5000000000 : ℝ)] ![(55115867317/6250000000000 : ℝ), (2553892745873/10000000000000 : ℝ), (73579218658363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-282582427/10000000000 : ℝ)|^65 ≤ (55115867317/6250000000000 : ℝ)^49
        have hw : |(-282582427/10000000000 : ℝ)|=(282582427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1786866083/5000000000 : ℝ)|^65 ≤ (2553892745873/10000000000000 : ℝ)^49
        have hw : |(1786866083/5000000000 : ℝ)|=(1786866083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3967563653/5000000000 : ℝ)|^65 ≤ (73579218658363/100000000000000 : ℝ)^49
        have hw : |(-3967563653/5000000000 : ℝ)|=(3967563653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1879723321/2000000000 : ℝ)*x 0 + (-4272287/39062500 : ℝ)*x 1 + (-63631129/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879723321/2000000000 : ℝ)^65 ≤ (92101877578573/100000000000000 : ℝ)^49 := by
    have hnat : (1879723321 : ℕ)^65*100000000000000^49 ≤ 92101877578573^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879723321 2000000000 92101877578573 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4272287/39062500 : ℝ)^65 ≤ (1061944781053/20000000000000 : ℝ)^49 := by
    have hnat : (4272287 : ℕ)^65*20000000000000^49 ≤ 1061944781053^49*39062500^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272287 39062500 1061944781053 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63631129/1000000000 : ℝ)^65 ≤ (2588398505733/100000000000000 : ℝ)^49 := by
    have hnat : (63631129 : ℕ)^65*100000000000000^49 ≤ 2588398505733^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63631129 1000000000 2588398505733 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1879723321/2000000000 : ℝ), (-4272287/39062500 : ℝ), (-63631129/1000000000 : ℝ)] ![(92101877578573/100000000000000 : ℝ), (1061944781053/20000000000000 : ℝ), (2588398505733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1879723321/2000000000 : ℝ)|^65 ≤ (92101877578573/100000000000000 : ℝ)^49
        have hw : |(1879723321/2000000000 : ℝ)|=(1879723321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4272287/39062500 : ℝ)|^65 ≤ (1061944781053/20000000000000 : ℝ)^49
        have hw : |(-4272287/39062500 : ℝ)|=(4272287/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63631129/1000000000 : ℝ)|^65 ≤ (2588398505733/100000000000000 : ℝ)^49
        have hw : |(-63631129/1000000000 : ℝ)|=(63631129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2020380487/5000000000 : ℝ)*x 0 + (22868153/39062500 : ℝ)*x 1 + (3060287459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020380487/5000000000 : ℝ)^65 ≤ (6011617385891/20000000000000 : ℝ)^49 := by
    have hnat : (2020380487 : ℕ)^65*20000000000000^49 ≤ 6011617385891^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020380487 5000000000 6011617385891 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22868153/39062500 : ℝ)^65 ≤ (24576115529659/50000000000000 : ℝ)^49 := by
    have hnat : (22868153 : ℕ)^65*50000000000000^49 ≤ 24576115529659^49*39062500^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22868153 39062500 24576115529659 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3060287459/10000000000 : ℝ)^65 ≤ (10394840996601/50000000000000 : ℝ)^49 := by
    have hnat : (3060287459 : ℕ)^65*50000000000000^49 ≤ 10394840996601^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3060287459 10000000000 10394840996601 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2020380487/5000000000 : ℝ), (22868153/39062500 : ℝ), (3060287459/10000000000 : ℝ)] ![(6011617385891/20000000000000 : ℝ), (24576115529659/50000000000000 : ℝ), (10394840996601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2020380487/5000000000 : ℝ)|^65 ≤ (6011617385891/20000000000000 : ℝ)^49
        have hw : |(2020380487/5000000000 : ℝ)|=(2020380487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22868153/39062500 : ℝ)|^65 ≤ (24576115529659/50000000000000 : ℝ)^49
        have hw : |(22868153/39062500 : ℝ)|=(22868153/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3060287459/10000000000 : ℝ)|^65 ≤ (10394840996601/50000000000000 : ℝ)^49
        have hw : |(3060287459/10000000000 : ℝ)|=(3060287459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2710615249/10000000000 : ℝ)*x 0 + (3226083577/10000000000 : ℝ)*x 1 + (-850537119/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710615249/10000000000 : ℝ)^65 ≤ (8849468513373/50000000000000 : ℝ)^49 := by
    have hnat : (2710615249 : ℕ)^65*50000000000000^49 ≤ 8849468513373^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710615249 10000000000 8849468513373 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3226083577/10000000000 : ℝ)^65 ≤ (557420800331/2500000000000 : ℝ)^49 := by
    have hnat : (3226083577 : ℕ)^65*2500000000000^49 ≤ 557420800331^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3226083577 10000000000 557420800331 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850537119/1250000000 : ℝ)^65 ≤ (7500528867483/12500000000000 : ℝ)^49 := by
    have hnat : (850537119 : ℕ)^65*12500000000000^49 ≤ 7500528867483^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850537119 1250000000 7500528867483 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710615249/10000000000 : ℝ), (3226083577/10000000000 : ℝ), (-850537119/1250000000 : ℝ)] ![(8849468513373/50000000000000 : ℝ), (557420800331/2500000000000 : ℝ), (7500528867483/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710615249/10000000000 : ℝ)|^65 ≤ (8849468513373/50000000000000 : ℝ)^49
        have hw : |(2710615249/10000000000 : ℝ)|=(2710615249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3226083577/10000000000 : ℝ)|^65 ≤ (557420800331/2500000000000 : ℝ)^49
        have hw : |(3226083577/10000000000 : ℝ)|=(3226083577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-850537119/1250000000 : ℝ)|^65 ≤ (7500528867483/12500000000000 : ℝ)^49
        have hw : |(-850537119/1250000000 : ℝ)|=(850537119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-27233119/625000000 : ℝ)*x 0 + (116214531/200000000 : ℝ)*x 1 + (-5909232843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27233119/625000000 : ℝ)^65 ≤ (1566318869703/100000000000000 : ℝ)^49 := by
    have hnat : (27233119 : ℕ)^65*100000000000000^49 ≤ 1566318869703^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27233119 625000000 1566318869703 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116214531/200000000 : ℝ)^65 ≤ (24334053761667/50000000000000 : ℝ)^49 := by
    have hnat : (116214531 : ℕ)^65*50000000000000^49 ≤ 24334053761667^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116214531 200000000 24334053761667 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5909232843/10000000000 : ℝ)^65 ≤ (49765573595887/100000000000000 : ℝ)^49 := by
    have hnat : (5909232843 : ℕ)^65*100000000000000^49 ≤ 49765573595887^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5909232843 10000000000 49765573595887 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27233119/625000000 : ℝ), (116214531/200000000 : ℝ), (-5909232843/10000000000 : ℝ)] ![(1566318869703/100000000000000 : ℝ), (24334053761667/50000000000000 : ℝ), (49765573595887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27233119/625000000 : ℝ)|^65 ≤ (1566318869703/100000000000000 : ℝ)^49
        have hw : |(-27233119/625000000 : ℝ)|=(27233119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(116214531/200000000 : ℝ)|^65 ≤ (24334053761667/50000000000000 : ℝ)^49
        have hw : |(116214531/200000000 : ℝ)|=(116214531/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5909232843/10000000000 : ℝ)|^65 ≤ (49765573595887/100000000000000 : ℝ)^49
        have hw : |(-5909232843/10000000000 : ℝ)|=(5909232843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2421588637/2500000000 : ℝ)*x 0 + (-40656219/1250000000 : ℝ)*x 1 + (-72480609/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2421588637/2500000000 : ℝ)^65 ≤ (95860854453477/100000000000000 : ℝ)^49 := by
    have hnat : (2421588637 : ℕ)^65*100000000000000^49 ≤ 95860854453477^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2421588637 2500000000 95860854453477 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40656219/1250000000 : ℝ)^65 ≤ (1062698999613/100000000000000 : ℝ)^49 := by
    have hnat : (40656219 : ℕ)^65*100000000000000^49 ≤ 1062698999613^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40656219 1250000000 1062698999613 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72480609/1000000000 : ℝ)^65 ≤ (3076446530141/100000000000000 : ℝ)^49 := by
    have hnat : (72480609 : ℕ)^65*100000000000000^49 ≤ 3076446530141^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72480609 1000000000 3076446530141 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2421588637/2500000000 : ℝ), (-40656219/1250000000 : ℝ), (-72480609/1000000000 : ℝ)] ![(95860854453477/100000000000000 : ℝ), (1062698999613/100000000000000 : ℝ), (3076446530141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2421588637/2500000000 : ℝ)|^65 ≤ (95860854453477/100000000000000 : ℝ)^49
        have hw : |(2421588637/2500000000 : ℝ)|=(2421588637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40656219/1250000000 : ℝ)|^65 ≤ (1062698999613/100000000000000 : ℝ)^49
        have hw : |(-40656219/1250000000 : ℝ)|=(40656219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-72480609/1000000000 : ℝ)|^65 ≤ (3076446530141/100000000000000 : ℝ)^49
        have hw : |(-72480609/1000000000 : ℝ)|=(72480609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1312549731/5000000000 : ℝ)*x 0 + (6278608919/10000000000 : ℝ)*x 1 + (3943719901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312549731/5000000000 : ℝ)^65 ≤ (4240519669433/25000000000000 : ℝ)^49 := by
    have hnat : (1312549731 : ℕ)^65*25000000000000^49 ≤ 4240519669433^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312549731 5000000000 4240519669433 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6278608919/10000000000 : ℝ)^65 ≤ (26966815254447/50000000000000 : ℝ)^49 := by
    have hnat : (6278608919 : ℕ)^65*50000000000000^49 ≤ 26966815254447^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6278608919 10000000000 26966815254447 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3943719901/10000000000 : ℝ)^65 ≤ (2910429079789/10000000000000 : ℝ)^49 := by
    have hnat : (3943719901 : ℕ)^65*10000000000000^49 ≤ 2910429079789^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3943719901 10000000000 2910429079789 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312549731/5000000000 : ℝ), (6278608919/10000000000 : ℝ), (3943719901/10000000000 : ℝ)] ![(4240519669433/25000000000000 : ℝ), (26966815254447/50000000000000 : ℝ), (2910429079789/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312549731/5000000000 : ℝ)|^65 ≤ (4240519669433/25000000000000 : ℝ)^49
        have hw : |(1312549731/5000000000 : ℝ)|=(1312549731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6278608919/10000000000 : ℝ)|^65 ≤ (26966815254447/50000000000000 : ℝ)^49
        have hw : |(6278608919/10000000000 : ℝ)|=(6278608919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3943719901/10000000000 : ℝ)|^65 ≤ (2910429079789/10000000000000 : ℝ)^49
        have hw : |(3943719901/10000000000 : ℝ)|=(3943719901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s0_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4619694289/10000000000 : ℝ)*x 0 + (2635541871/5000000000 : ℝ)*x 1 + (-62410569/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4619694289/10000000000 : ℝ)^65 ≤ (7180078416223/20000000000000 : ℝ)^49 := by
    have hnat : (4619694289 : ℕ)^65*20000000000000^49 ≤ 7180078416223^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4619694289 10000000000 7180078416223 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635541871/5000000000 : ℝ)^65 ≤ (42765319915479/100000000000000 : ℝ)^49 := by
    have hnat : (2635541871 : ℕ)^65*100000000000000^49 ≤ 42765319915479^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635541871 5000000000 42765319915479 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62410569/200000000 : ℝ)^65 ≤ (10667143997631/50000000000000 : ℝ)^49 := by
    have hnat : (62410569 : ℕ)^65*50000000000000^49 ≤ 10667143997631^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62410569 200000000 10667143997631 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4619694289/10000000000 : ℝ), (2635541871/5000000000 : ℝ), (-62410569/200000000 : ℝ)] ![(7180078416223/20000000000000 : ℝ), (42765319915479/100000000000000 : ℝ), (10667143997631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4619694289/10000000000 : ℝ)|^65 ≤ (7180078416223/20000000000000 : ℝ)^49
        have hw : |(4619694289/10000000000 : ℝ)|=(4619694289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635541871/5000000000 : ℝ)|^65 ≤ (42765319915479/100000000000000 : ℝ)^49
        have hw : |(2635541871/5000000000 : ℝ)|=(2635541871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62410569/200000000 : ℝ)|^65 ≤ (10667143997631/50000000000000 : ℝ)^49
        have hw : |(-62410569/200000000 : ℝ)|=(62410569/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2672470721/10000000000 : ℝ)*x 0 + (4498637609/10000000000 : ℝ)*x 1 + (-1149608057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672470721/10000000000 : ℝ)^65 ≤ (4342326761567/25000000000000 : ℝ)^49 := by
    have hnat : (2672470721 : ℕ)^65*25000000000000^49 ≤ 4342326761567^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672470721 10000000000 4342326761567 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498637609/10000000000 : ℝ)^65 ≤ (17328913891679/50000000000000 : ℝ)^49 := by
    have hnat : (4498637609 : ℕ)^65*50000000000000^49 ≤ 17328913891679^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498637609 10000000000 17328913891679 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1149608057/2000000000 : ℝ)^65 ≤ (9594573032511/20000000000000 : ℝ)^49 := by
    have hnat : (1149608057 : ℕ)^65*20000000000000^49 ≤ 9594573032511^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149608057 2000000000 9594573032511 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2672470721/10000000000 : ℝ), (4498637609/10000000000 : ℝ), (-1149608057/2000000000 : ℝ)] ![(4342326761567/25000000000000 : ℝ), (17328913891679/50000000000000 : ℝ), (9594573032511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2672470721/10000000000 : ℝ)|^65 ≤ (4342326761567/25000000000000 : ℝ)^49
        have hw : |(-2672470721/10000000000 : ℝ)|=(2672470721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498637609/10000000000 : ℝ)|^65 ≤ (17328913891679/50000000000000 : ℝ)^49
        have hw : |(4498637609/10000000000 : ℝ)|=(4498637609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1149608057/2000000000 : ℝ)|^65 ≤ (9594573032511/20000000000000 : ℝ)^49
        have hw : |(-1149608057/2000000000 : ℝ)|=(1149608057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (820744037/1250000000 : ℝ)*x 0 + (-290494851/1000000000 : ℝ)*x 1 + (-3342059683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (820744037/1250000000 : ℝ)^65 ≤ (1430803011079/2500000000000 : ℝ)^49 := by
    have hnat : (820744037 : ℕ)^65*2500000000000^49 ≤ 1430803011079^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820744037 1250000000 1430803011079 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290494851/1000000000 : ℝ)^65 ≤ (9700781196433/50000000000000 : ℝ)^49 := by
    have hnat : (290494851 : ℕ)^65*50000000000000^49 ≤ 9700781196433^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290494851 1000000000 9700781196433 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3342059683/10000000000 : ℝ)^65 ≤ (23366317150141/100000000000000 : ℝ)^49 := by
    have hnat : (3342059683 : ℕ)^65*100000000000000^49 ≤ 23366317150141^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3342059683 10000000000 23366317150141 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(820744037/1250000000 : ℝ), (-290494851/1000000000 : ℝ), (-3342059683/10000000000 : ℝ)] ![(1430803011079/2500000000000 : ℝ), (9700781196433/50000000000000 : ℝ), (23366317150141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(820744037/1250000000 : ℝ)|^65 ≤ (1430803011079/2500000000000 : ℝ)^49
        have hw : |(820744037/1250000000 : ℝ)|=(820744037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-290494851/1000000000 : ℝ)|^65 ≤ (9700781196433/50000000000000 : ℝ)^49
        have hw : |(-290494851/1000000000 : ℝ)|=(290494851/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3342059683/10000000000 : ℝ)|^65 ≤ (23366317150141/100000000000000 : ℝ)^49
        have hw : |(-3342059683/10000000000 : ℝ)|=(3342059683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1973060837/5000000000 : ℝ)*x 0 + (52582099/100000000 : ℝ)*x 1 + (3855660079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1973060837/5000000000 : ℝ)^65 ≤ (29127805710443/100000000000000 : ℝ)^49 := by
    have hnat : (1973060837 : ℕ)^65*100000000000000^49 ≤ 29127805710443^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973060837 5000000000 29127805710443 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52582099/100000000 : ℝ)^65 ≤ (10656705442709/25000000000000 : ℝ)^49 := by
    have hnat : (52582099 : ℕ)^65*25000000000000^49 ≤ 10656705442709^49*100000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52582099 100000000 10656705442709 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3855660079/10000000000 : ℝ)^65 ≤ (28245372502517/100000000000000 : ℝ)^49 := by
    have hnat : (3855660079 : ℕ)^65*100000000000000^49 ≤ 28245372502517^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3855660079 10000000000 28245372502517 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1973060837/5000000000 : ℝ), (52582099/100000000 : ℝ), (3855660079/10000000000 : ℝ)] ![(29127805710443/100000000000000 : ℝ), (10656705442709/25000000000000 : ℝ), (28245372502517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1973060837/5000000000 : ℝ)|^65 ≤ (29127805710443/100000000000000 : ℝ)^49
        have hw : |(1973060837/5000000000 : ℝ)|=(1973060837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52582099/100000000 : ℝ)|^65 ≤ (10656705442709/25000000000000 : ℝ)^49
        have hw : |(52582099/100000000 : ℝ)|=(52582099/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3855660079/10000000000 : ℝ)|^65 ≤ (28245372502517/100000000000000 : ℝ)^49
        have hw : |(3855660079/10000000000 : ℝ)|=(3855660079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301079_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1933383949/5000000000 : ℝ)*x 0 + (4886450529/10000000000 : ℝ)*x 1 + (-270784113/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1933383949/5000000000 : ℝ)^65 ≤ (28353366279527/100000000000000 : ℝ)^49 := by
    have hnat : (1933383949 : ℕ)^65*100000000000000^49 ≤ 28353366279527^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933383949 5000000000 28353366279527 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4886450529/10000000000 : ℝ)^65 ≤ (38675894373489/100000000000000 : ℝ)^49 := by
    have hnat : (4886450529 : ℕ)^65*100000000000000^49 ≤ 38675894373489^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886450529 10000000000 38675894373489 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270784113/625000000 : ℝ)^65 ≤ (32970739336809/100000000000000 : ℝ)^49 := by
    have hnat : (270784113 : ℕ)^65*100000000000000^49 ≤ 32970739336809^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270784113 625000000 32970739336809 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1933383949/5000000000 : ℝ), (4886450529/10000000000 : ℝ), (-270784113/625000000 : ℝ)] ![(28353366279527/100000000000000 : ℝ), (38675894373489/100000000000000 : ℝ), (32970739336809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1933383949/5000000000 : ℝ)|^65 ≤ (28353366279527/100000000000000 : ℝ)^49
        have hw : |(1933383949/5000000000 : ℝ)|=(1933383949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4886450529/10000000000 : ℝ)|^65 ≤ (38675894373489/100000000000000 : ℝ)^49
        have hw : |(4886450529/10000000000 : ℝ)|=(4886450529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270784113/625000000 : ℝ)|^65 ≤ (32970739336809/100000000000000 : ℝ)^49
        have hw : |(-270784113/625000000 : ℝ)|=(270784113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301079 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((127801487/156250000 : ℝ)*X 1 0+(-1542451073/10000000000 : ℝ)*X 1 1+(-2395706983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((819688979/2500000000 : ℝ)*X 2 0+(3040146939/5000000000 : ℝ)*X 2 1+(3573149269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1756788659/5000000000 : ℝ)*X 0 0+(1065213007/2000000000 : ℝ)*X 0 1+(-840645727/2000000000 : ℝ)*X 0 2+(1756788659/5000000000 : ℝ)*X 1 0+(1065213007/2000000000 : ℝ)*X 1 1+(-840645727/2000000000 : ℝ)*X 1 2+(1756788659/5000000000 : ℝ)*X 2 0+(1065213007/2000000000 : ℝ)*X 2 1+(-840645727/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-833787213/5000000000 : ℝ)*X 0 0+(2888118931/10000000000 : ℝ)*X 0 1+(-7761908371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((8072261987/10000000000 : ℝ)*X 1 0+(-520143/19531250 : ℝ)*X 1 1+(-136038093/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((278244079/2000000000 : ℝ)*X 2 0+(8032811997/10000000000 : ℝ)*X 2 1+(2735024053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((94877731/400000000 : ℝ)*X 0 0+(7674805877/10000000000 : ℝ)*X 0 1+(-147879401/625000000 : ℝ)*X 0 2+(94877731/400000000 : ℝ)*X 1 0+(7674805877/10000000000 : ℝ)*X 1 1+(-147879401/625000000 : ℝ)*X 1 2+(94877731/400000000 : ℝ)*X 2 0+(7674805877/10000000000 : ℝ)*X 2 1+(-147879401/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-282582427/10000000000 : ℝ)*X 0 0+(1786866083/5000000000 : ℝ)*X 0 1+(-3967563653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1879723321/2000000000 : ℝ)*X 1 0+(-4272287/39062500 : ℝ)*X 1 1+(-63631129/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2020380487/5000000000 : ℝ)*X 2 0+(22868153/39062500 : ℝ)*X 2 1+(3060287459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2710615249/10000000000 : ℝ)*X 0 0+(3226083577/10000000000 : ℝ)*X 0 1+(-850537119/1250000000 : ℝ)*X 0 2+(2710615249/10000000000 : ℝ)*X 1 0+(3226083577/10000000000 : ℝ)*X 1 1+(-850537119/1250000000 : ℝ)*X 1 2+(2710615249/10000000000 : ℝ)*X 2 0+(3226083577/10000000000 : ℝ)*X 2 1+(-850537119/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-27233119/625000000 : ℝ)*X 0 0+(116214531/200000000 : ℝ)*X 0 1+(-5909232843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2421588637/2500000000 : ℝ)*X 1 0+(-40656219/1250000000 : ℝ)*X 1 1+(-72480609/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1312549731/5000000000 : ℝ)*X 2 0+(6278608919/10000000000 : ℝ)*X 2 1+(3943719901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4619694289/10000000000 : ℝ)*X 0 0+(2635541871/5000000000 : ℝ)*X 0 1+(-62410569/200000000 : ℝ)*X 0 2+(4619694289/10000000000 : ℝ)*X 1 0+(2635541871/5000000000 : ℝ)*X 1 1+(-62410569/200000000 : ℝ)*X 1 2+(4619694289/10000000000 : ℝ)*X 2 0+(2635541871/5000000000 : ℝ)*X 2 1+(-62410569/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((927/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(927/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5628212621311590571683/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167261734111/250000000000 : ℝ)*(base39) + (878602395497/1000000000000 : ℝ)*(base49) + (9601611/1000000000000 : ℝ)*(base53) + (1110525777/1953125000 : ℝ)*(base60) + (253325927573/100000000000 : ℝ)*(major_s0_0) + (253325927573/100000000000 : ℝ)*(major_s0_1) + (1266624837059/500000000000 : ℝ)*(major_s0_2) + (39726077/1000000000000 : ℝ)*(sp_s0_1) + (54937/62500000000 : ℝ)*(sp_s0_6) + (3353929113733/1000000000000 : ℝ)*(sp_s0_7) + (3353924385843/1000000000000 : ℝ)*(sp_s0_8) + (3353973713531/1000000000000 : ℝ)*(sp_s0_9) + (428135051697/250000000000 : ℝ)*(sp_s0_13) + (17499093/500000000000 : ℝ)*(sp_s0_14) + (85627054289/50000000000 : ℝ)*(f.failure) + (3353973713531/1000000000000 : ℝ)*(f.sum) + (252303363934773/2500000000000000000000000000 : ℝ)*base62 + (1967315387818937/5000000000000000000000000000 : ℝ)*base65 + (110347260843303/1000000000000000000000000000 : ℝ)*base66 + (1790858386927649/5000000000000000000000000000 : ℝ)*base69 + (84673627616137/1250000000000000000000000000 : ℝ)*base70 + (1032469628059439/1000000000000000000000000000 : ℝ)*base73 + (17833521240561/1000000000000000000000000000 : ℝ)*base75 + (487684899243303/1000000000000000000000000000 : ℝ)*base77 + (38178578452017/125000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (991/1250000000000000 : ℝ)*base86 + (991/1250000000000000 : ℝ)*base88 + (259/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((30101/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(30101/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19556607248039744520657/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1022096343681/1000000000000 : ℝ)*(base39) + (170069/50000000000 : ℝ)*(base40) + (483345631981/1000000000000 : ℝ)*(base49) + (371535765461/500000000000 : ℝ)*(base60) + (3096289390597/1000000000000 : ℝ)*(major_s0_0) + (3096289390597/1000000000000 : ℝ)*(major_s0_1) + (3096289390597/1000000000000 : ℝ)*(major_s0_2) + (15983417/1000000000000 : ℝ)*(sp_s0_1) + (24527533/1000000000000 : ℝ)*(sp_s0_7) + (4099389352907/1000000000000 : ℝ)*(sp_s0_14) + (2049660051301/500000000000 : ℝ)*(sp_s0_15) + (102485347011/25000000000 : ℝ)*(sp_s0_16) + (2093162293203/1000000000000 : ℝ)*(sp_s0_20) + (77794421/1000000000000 : ℝ)*(sp_s0_22) + (2093162293203/1000000000000 : ℝ)*(f.failure) + (102485347011/25000000000 : ℝ)*(f.sum) + (487086648741587/1250000000000000000000000000 : ℝ)*base63 + (5276933638376129/10000000000000000000000000000 : ℝ)*base64 + (5008137873443433/10000000000000000000000000000 : ℝ)*base67 + (3206427853443433/10000000000000000000000000000 : ℝ)*base68 + (877767504409781/5000000000000000000000000000 : ℝ)*base70 + (2581745914623871/10000000000000000000000000000 : ℝ)*base73 + (354428384623871/10000000000000000000000000000 : ℝ)*base74 + (4403684383443433/10000000000000000000000000000 : ℝ)*base76 + (141061761741587/1250000000000000000000000000 : ℝ)*base78 + (15143/25000000000000000 : ℝ)*base87 + (15143/25000000000000000 : ℝ)*base89 + (15143/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1193/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1193/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9838154480314214272257/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23401/12500000000 : ℝ)*(base11) + (458231175923/500000000000 : ℝ)*(base39) + (105357116039/200000000000 : ℝ)*(base49) + (62109/62500000000 : ℝ)*(base50) + (2456146323871/1000000000000 : ℝ)*(major_s0_0) + (2456146323871/1000000000000 : ℝ)*(major_s0_1) + (2456146323871/1000000000000 : ℝ)*(major_s0_2) + (46837719/1000000000000 : ℝ)*(sp_s0_2) + (9052689/1000000000000 : ℝ)*(sp_s0_9) + (1099661/1000000000000 : ℝ)*(sp_s0_15) + (1625939246747/500000000000 : ℝ)*(sp_s0_21) + (3251879265913/1000000000000 : ℝ)*(sp_s0_22) + (1625912237583/500000000000 : ℝ)*(sp_s0_23) + (1660410970411/1000000000000 : ℝ)*(sp_s0_27) + (1660410970411/1000000000000 : ℝ)*(f.failure) + (1625940182787/500000000000 : ℝ)*(f.sum) + (475364292535441/1250000000000000000000000000 : ℝ)*base63 + (3680382383459053/10000000000000000000000000000 : ℝ)*base65 + (35642196742581/10000000000000000000000000000 : ℝ)*base66 + (3707882580742581/10000000000000000000000000000 : ℝ)*base69 + (221377620100817/5000000000000000000000000000 : ℝ)*base71 + (51418144540947/10000000000000000000000000000 : ℝ)*base72 + (3693162724540947/10000000000000000000000000000 : ℝ)*base75 + (3269700857742581/10000000000000000000000000000 : ℝ)*base77 + (48881989089559/1250000000000000000000000000 : ℝ)*base79 + (5809/25000000000000000 : ℝ)*base86 + (5809/25000000000000000 : ℝ)*base88 + (5809/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (927/2000 : ℝ) ^ (129/32 : ℝ) ≤ (4505707638289523009/100000000000000000000 : ℝ) := by
    have hpowers : (927/2000 : ℝ)^129 ≤ (4505707638289523009/100000000000000000000 : ℝ)^32 := by
      have hnat : (927 : ℕ)^129*100000000000000000000^32 ≤ 4505707638289523009^32*2000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        927 2000 4505707638289523009 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (927/2000 : ℝ)) (X := (4505707638289523009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (104505707638289523009/100000000000000000000 : ℝ) ≤ (10109924435023629/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (104505707638289523009/100000000000000000000 : ℝ)^32 ≤ (10109924435023629/10000000000000000 : ℝ)^129 := by
      have hnat : (104505707638289523009 : ℕ)^32*10000000000000000^129 ≤ 10109924435023629^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104505707638289523009 100000000000000000000 10109924435023629 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10109924435023629/10000000000000000 : ℝ)) (X := (104505707638289523009/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (54505707638289523009/50000000000000000000 : ℝ) ≤ (10216340860398417/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (54505707638289523009/50000000000000000000 : ℝ)^32 ≤ (10216340860398417/10000000000000000 : ℝ)^129 := by
      have hnat : (54505707638289523009 : ℕ)^32*10000000000000000^129 ≤ 10216340860398417^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54505707638289523009 50000000000000000000 10216340860398417 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10216340860398417/10000000000000000 : ℝ)) (X := (54505707638289523009/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(109924435023629/4635000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(86097431533/3750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (927/2000 : ℝ)) (alpha := (109924435023629/4635000000000000 : ℝ)) (beta := (86097431533/3750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (927/2000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(109924435023629/4635000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(86097431533/3750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (30101/50000 : ℝ) ^ (129/32 : ℝ) ≤ (12928749439272504403/100000000000000000000 : ℝ) := by
    have hpowers : (30101/50000 : ℝ)^129 ≤ (12928749439272504403/100000000000000000000 : ℝ)^32 := by
      have hnat : (30101 : ℕ)^129*100000000000000000000^32 ≤ 12928749439272504403^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30101 50000 12928749439272504403 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30101/50000 : ℝ)) (X := (12928749439272504403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (112928749439272504403/100000000000000000000 : ℝ) ≤ (1030620544230741/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (112928749439272504403/100000000000000000000 : ℝ)^32 ≤ (1030620544230741/1000000000000000 : ℝ)^129 := by
      have hnat : (112928749439272504403 : ℕ)^32*1000000000000000^129 ≤ 1030620544230741^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112928749439272504403 100000000000000000000 1030620544230741 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1030620544230741/1000000000000000 : ℝ)) (X := (112928749439272504403/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (62928749439272504403/50000000000000000000 : ℝ) ≤ (5293540186510267/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (62928749439272504403/50000000000000000000 : ℝ)^32 ≤ (5293540186510267/5000000000000000 : ℝ)^129 := by
      have hnat : (62928749439272504403 : ℕ)^32*5000000000000000^129 ≤ 5293540186510267^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62928749439272504403 50000000000000000000 5293540186510267 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5293540186510267/5000000000000000 : ℝ)) (X := (62928749439272504403/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(30620544230741/602020000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(70218732678281/1505050000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (30101/50000 : ℝ)) (alpha := (30620544230741/602020000000000 : ℝ)) (beta := (70218732678281/1505050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (30101/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(30620544230741/602020000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(70218732678281/1505050000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1193/2500 : ℝ) ^ (129/32 : ℝ) ≤ (5067119290299667899/100000000000000000000 : ℝ) := by
    have hpowers : (1193/2500 : ℝ)^129 ≤ (5067119290299667899/100000000000000000000 : ℝ)^32 := by
      have hnat : (1193 : ℕ)^129*100000000000000000000^32 ≤ 5067119290299667899^32*2500^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1193 2500 5067119290299667899 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1193/2500 : ℝ)) (X := (5067119290299667899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (105067119290299667899/100000000000000000000 : ℝ) ≤ (2024673970501261/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (105067119290299667899/100000000000000000000 : ℝ)^32 ≤ (2024673970501261/2000000000000000 : ℝ)^129 := by
      have hnat : (105067119290299667899 : ℕ)^32*2000000000000000^129 ≤ 2024673970501261^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105067119290299667899 100000000000000000000 2024673970501261 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2024673970501261/2000000000000000 : ℝ)) (X := (105067119290299667899/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (55067119290299667899/50000000000000000000 : ℝ) ≤ (10242343659202691/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (55067119290299667899/50000000000000000000 : ℝ)^32 ≤ (10242343659202691/10000000000000000 : ℝ)^129 := by
      have hnat : (55067119290299667899 : ℕ)^32*10000000000000000^129 ≤ 10242343659202691^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55067119290299667899 50000000000000000000 10242343659202691 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10242343659202691/10000000000000000 : ℝ)) (X := (55067119290299667899/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(24673970501261/954400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(59486903348193/2386000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1193/2500 : ℝ)) (alpha := (24673970501261/954400000000000 : ℝ)) (beta := (59486903348193/2386000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1193/2500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(24673970501261/954400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(59486903348193/2386000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2672470721/10000000000 : ℝ)*X 0 0+(4498637609/10000000000 : ℝ)*X 0 1+(-1149608057/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((820744037/1250000000 : ℝ)*X 1 0+(-290494851/1000000000 : ℝ)*X 1 1+(-3342059683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1973060837/5000000000 : ℝ)*X 2 0+(52582099/100000000 : ℝ)*X 2 1+(3855660079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1933383949/5000000000 : ℝ)*X 0 0+(4886450529/10000000000 : ℝ)*X 0 1+(-270784113/625000000 : ℝ)*X 0 2+(1933383949/5000000000 : ℝ)*X 1 0+(4886450529/10000000000 : ℝ)*X 1 1+(-270784113/625000000 : ℝ)*X 1 2+(1933383949/5000000000 : ℝ)*X 2 0+(4886450529/10000000000 : ℝ)*X 2 1+(-270784113/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-54111860087688797145136313103381/9246951947500000000000000000000 : ℝ) := by norm_num
    linear_combination (8897/100000000000 : ℝ)*(base5) + (13411/1000000000000 : ℝ)*(base18) + (76793/1000000000000 : ℝ)*(base23) + (9233/200000000000 : ℝ)*(base29) + (180057193103/500000000000 : ℝ)*(base39) + (1621/500000000000 : ℝ)*(base44) + (253810432401/1000000000000 : ℝ)*(base49) + (29992346701/200000000000 : ℝ)*(base60) + (36981/25000 : ℝ)*(major_s1_0) + (739619998379/500000000000 : ℝ)*(major_s1_1) + (36981/25000 : ℝ)*(major_s1_2) + (975309853359/500000000000 : ℝ)*(sp_s1_0) + (121913730629/62500000000 : ℝ)*(sp_s1_1) + (390123943779/200000000000 : ℝ)*(sp_s1_2) + (999999861623/1000000000000 : ℝ)*(sp_s1_6) + (975309853359/500000000000 : ℝ)*(f.sum) + (23712801264185273/897762325000000000000000000000 : ℝ)*base63 + (2910361053997/11930000000000000000000000 : ℝ)*base64 + (2276426096543/12040400000000000000000000 : ℝ)*base67 + (2379358190093/5965000000000000000000000 : ℝ)*base69 + (265968119565833/1228790000000000000000000000 : ℝ)*base70 + (109626997/312500000000000000000 : ℝ)*base72 + (249938565499209/752525000000000000000000000 : ℝ)*base74 + (256419653901/1030000000000000000000000 : ℝ)*base76 + (934860606137/15050500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p001_b037 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl
  · exact collision_c301079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301080 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b037 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

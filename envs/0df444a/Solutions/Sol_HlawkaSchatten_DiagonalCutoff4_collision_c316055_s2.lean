-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:16.594827+00:00
-- url     : https://prove2.me/submissions/4e7253b0-4bb7-4b0b-ab9a-d226eddeb178

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
theorem collision_support_c316055_s2_s2_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025414961/10000000000 : ℝ)*x 0 + (5563913829/10000000000 : ℝ)*x 1 + (1184942339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025414961/10000000000 : ℝ)^77 ≤ (6661715083821/50000000000000 : ℝ)^61 := by
    have hnat : (2025414961 : ℕ)^77*50000000000000^61 ≤ 6661715083821^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025414961 10000000000 6661715083821 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5563913829/10000000000 : ℝ)^77 ≤ (2385420402651/5000000000000 : ℝ)^61 := by
    have hnat : (5563913829 : ℕ)^77*5000000000000^61 ≤ 2385420402651^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5563913829 10000000000 2385420402651 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184942339/2500000000 : ℝ)^77 ≤ (19484080877207/50000000000000 : ℝ)^61 := by
    have hnat : (1184942339 : ℕ)^77*50000000000000^61 ≤ 19484080877207^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184942339 2500000000 19484080877207 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025414961/10000000000 : ℝ), (5563913829/10000000000 : ℝ), (1184942339/2500000000 : ℝ)] ![(6661715083821/50000000000000 : ℝ), (2385420402651/5000000000000 : ℝ), (19484080877207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025414961/10000000000 : ℝ)|^77 ≤ (6661715083821/50000000000000 : ℝ)^61
        have hw : |(-2025414961/10000000000 : ℝ)|=(2025414961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5563913829/10000000000 : ℝ)|^77 ≤ (2385420402651/5000000000000 : ℝ)^61
        have hw : |(5563913829/10000000000 : ℝ)|=(5563913829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1184942339/2500000000 : ℝ)|^77 ≤ (19484080877207/50000000000000 : ℝ)^61
        have hw : |(1184942339/2500000000 : ℝ)|=(1184942339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (947435561/2000000000 : ℝ)*x 0 + (-1189609257/10000000000 : ℝ)*x 1 + (385023461/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947435561/2000000000 : ℝ)^77 ≤ (38941268571037/100000000000000 : ℝ)^61 := by
    have hnat : (947435561 : ℕ)^77*100000000000000^61 ≤ 38941268571037^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947435561 2000000000 38941268571037 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1189609257/10000000000 : ℝ)^77 ≤ (3402964696567/50000000000000 : ℝ)^61 := by
    have hnat : (1189609257 : ℕ)^77*50000000000000^61 ≤ 3402964696567^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1189609257 10000000000 3402964696567 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385023461/625000000 : ℝ)^77 ≤ (27126401009131/50000000000000 : ℝ)^61 := by
    have hnat : (385023461 : ℕ)^77*50000000000000^61 ≤ 27126401009131^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385023461 625000000 27126401009131 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(947435561/2000000000 : ℝ), (-1189609257/10000000000 : ℝ), (385023461/625000000 : ℝ)] ![(38941268571037/100000000000000 : ℝ), (3402964696567/50000000000000 : ℝ), (27126401009131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(947435561/2000000000 : ℝ)|^77 ≤ (38941268571037/100000000000000 : ℝ)^61
        have hw : |(947435561/2000000000 : ℝ)|=(947435561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1189609257/10000000000 : ℝ)|^77 ≤ (3402964696567/50000000000000 : ℝ)^61
        have hw : |(-1189609257/10000000000 : ℝ)|=(1189609257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(385023461/625000000 : ℝ)|^77 ≤ (27126401009131/50000000000000 : ℝ)^61
        have hw : |(385023461/625000000 : ℝ)|=(385023461/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4730502403/10000000000 : ℝ)*x 0 + (1393731411/2500000000 : ℝ)*x 1 + (-1011317963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4730502403/10000000000 : ℝ)^77 ≤ (19436007001223/50000000000000 : ℝ)^61 := by
    have hnat : (4730502403 : ℕ)^77*50000000000000^61 ≤ 19436007001223^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4730502403 10000000000 19436007001223 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393731411/2500000000 : ℝ)^77 ≤ (47827627467051/100000000000000 : ℝ)^61 := by
    have hnat : (1393731411 : ℕ)^77*100000000000000^61 ≤ 47827627467051^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393731411 2500000000 47827627467051 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011317963/5000000000 : ℝ)^77 ≤ (13300358512033/100000000000000 : ℝ)^61 := by
    have hnat : (1011317963 : ℕ)^77*100000000000000^61 ≤ 13300358512033^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011317963 5000000000 13300358512033 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4730502403/10000000000 : ℝ), (1393731411/2500000000 : ℝ), (-1011317963/5000000000 : ℝ)] ![(19436007001223/50000000000000 : ℝ), (47827627467051/100000000000000 : ℝ), (13300358512033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4730502403/10000000000 : ℝ)|^77 ≤ (19436007001223/50000000000000 : ℝ)^61
        have hw : |(4730502403/10000000000 : ℝ)|=(4730502403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1393731411/2500000000 : ℝ)|^77 ≤ (47827627467051/100000000000000 : ℝ)^61
        have hw : |(1393731411/2500000000 : ℝ)|=(1393731411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1011317963/5000000000 : ℝ)|^77 ≤ (13300358512033/100000000000000 : ℝ)^61
        have hw : |(-1011317963/5000000000 : ℝ)|=(1011317963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3023978379/5000000000 : ℝ)*x 0 + (3910825359/10000000000 : ℝ)*x 1 + (119515647/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3023978379/5000000000 : ℝ)^77 ≤ (53006082416043/100000000000000 : ℝ)^61 := by
    have hnat : (3023978379 : ℕ)^77*100000000000000^61 ≤ 53006082416043^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3023978379 5000000000 53006082416043 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3910825359/10000000000 : ℝ)^77 ≤ (15285950167703/50000000000000 : ℝ)^61 := by
    have hnat : (3910825359 : ℕ)^77*50000000000000^61 ≤ 15285950167703^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3910825359 10000000000 15285950167703 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119515647/500000000 : ℝ)^77 ≤ (256594019269/1562500000000 : ℝ)^61 := by
    have hnat : (119515647 : ℕ)^77*1562500000000^61 ≤ 256594019269^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119515647 500000000 256594019269 1562500000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3023978379/5000000000 : ℝ), (3910825359/10000000000 : ℝ), (119515647/500000000 : ℝ)] ![(53006082416043/100000000000000 : ℝ), (15285950167703/50000000000000 : ℝ), (256594019269/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3023978379/5000000000 : ℝ)|^77 ≤ (53006082416043/100000000000000 : ℝ)^61
        have hw : |(3023978379/5000000000 : ℝ)|=(3023978379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3910825359/10000000000 : ℝ)|^77 ≤ (15285950167703/50000000000000 : ℝ)^61
        have hw : |(3910825359/10000000000 : ℝ)|=(3910825359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119515647/500000000 : ℝ)|^77 ≤ (256594019269/1562500000000 : ℝ)^61
        have hw : |(119515647/500000000 : ℝ)|=(119515647/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-886871247/5000000000 : ℝ)*x 0 + (5001524747/10000000000 : ℝ)*x 1 + (220035001/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (886871247/5000000000 : ℝ)^77 ≤ (2253763063177/20000000000000 : ℝ)^61 := by
    have hnat : (886871247 : ℕ)^77*20000000000000^61 ≤ 2253763063177^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886871247 5000000000 2253763063177 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001524747/10000000000 : ℝ)^77 ≤ (5213009064731/12500000000000 : ℝ)^61 := by
    have hnat : (5001524747 : ℕ)^77*12500000000000^61 ≤ 5213009064731^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001524747 10000000000 5213009064731 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220035001/400000000 : ℝ)^77 ≤ (47027112145469/100000000000000 : ℝ)^61 := by
    have hnat : (220035001 : ℕ)^77*100000000000000^61 ≤ 47027112145469^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220035001 400000000 47027112145469 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-886871247/5000000000 : ℝ), (5001524747/10000000000 : ℝ), (220035001/400000000 : ℝ)] ![(2253763063177/20000000000000 : ℝ), (5213009064731/12500000000000 : ℝ), (47027112145469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-886871247/5000000000 : ℝ)|^77 ≤ (2253763063177/20000000000000 : ℝ)^61
        have hw : |(-886871247/5000000000 : ℝ)|=(886871247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001524747/10000000000 : ℝ)|^77 ≤ (5213009064731/12500000000000 : ℝ)^61
        have hw : |(5001524747/10000000000 : ℝ)|=(5001524747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220035001/400000000 : ℝ)|^77 ≤ (47027112145469/100000000000000 : ℝ)^61
        have hw : |(220035001/400000000 : ℝ)|=(220035001/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (928280779/2000000000 : ℝ)*x 0 + (-614253557/10000000000 : ℝ)*x 1 + (1648013777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928280779/2000000000 : ℝ)^77 ≤ (37950117907999/100000000000000 : ℝ)^61 := by
    have hnat : (928280779 : ℕ)^77*100000000000000^61 ≤ 37950117907999^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928280779 2000000000 37950117907999 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (614253557/10000000000 : ℝ)^77 ≤ (369357777651/12500000000000 : ℝ)^61 := by
    have hnat : (614253557 : ℕ)^77*12500000000000^61 ≤ 369357777651^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614253557 10000000000 369357777651 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1648013777/2500000000 : ℝ)^77 ≤ (295475099267/500000000000 : ℝ)^61 := by
    have hnat : (1648013777 : ℕ)^77*500000000000^61 ≤ 295475099267^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648013777 2500000000 295475099267 500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(928280779/2000000000 : ℝ), (-614253557/10000000000 : ℝ), (1648013777/2500000000 : ℝ)] ![(37950117907999/100000000000000 : ℝ), (369357777651/12500000000000 : ℝ), (295475099267/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(928280779/2000000000 : ℝ)|^77 ≤ (37950117907999/100000000000000 : ℝ)^61
        have hw : |(928280779/2000000000 : ℝ)|=(928280779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-614253557/10000000000 : ℝ)|^77 ≤ (369357777651/12500000000000 : ℝ)^61
        have hw : |(-614253557/10000000000 : ℝ)|=(614253557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1648013777/2500000000 : ℝ)|^77 ≤ (295475099267/500000000000 : ℝ)^61
        have hw : |(1648013777/2500000000 : ℝ)|=(1648013777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2317347161/5000000000 : ℝ)*x 0 + (1546352579/2500000000 : ℝ)*x 1 + (-129664747/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2317347161/5000000000 : ℝ)^77 ≤ (37880881079429/100000000000000 : ℝ)^61 := by
    have hnat : (2317347161 : ℕ)^77*100000000000000^61 ≤ 37880881079429^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317347161 5000000000 37880881079429 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1546352579/2500000000 : ℝ)^77 ≤ (13632814029081/25000000000000 : ℝ)^61 := by
    have hnat : (1546352579 : ℕ)^77*25000000000000^61 ≤ 13632814029081^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546352579 2500000000 13632814029081 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129664747/1000000000 : ℝ)^77 ≤ (1896965697377/25000000000000 : ℝ)^61 := by
    have hnat : (129664747 : ℕ)^77*25000000000000^61 ≤ 1896965697377^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129664747 1000000000 1896965697377 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2317347161/5000000000 : ℝ), (1546352579/2500000000 : ℝ), (-129664747/1000000000 : ℝ)] ![(37880881079429/100000000000000 : ℝ), (13632814029081/25000000000000 : ℝ), (1896965697377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2317347161/5000000000 : ℝ)|^77 ≤ (37880881079429/100000000000000 : ℝ)^61
        have hw : |(2317347161/5000000000 : ℝ)|=(2317347161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1546352579/2500000000 : ℝ)|^77 ≤ (13632814029081/25000000000000 : ℝ)^61
        have hw : |(1546352579/2500000000 : ℝ)|=(1546352579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129664747/1000000000 : ℝ)|^77 ≤ (1896965697377/25000000000000 : ℝ)^61
        have hw : |(-129664747/1000000000 : ℝ)|=(129664747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5380644423/10000000000 : ℝ)*x 0 + (5415722271/10000000000 : ℝ)*x 1 + (68652503/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380644423/10000000000 : ℝ)^77 ≤ (22866697995591/50000000000000 : ℝ)^61 := by
    have hnat : (5380644423 : ℕ)^77*50000000000000^61 ≤ 22866697995591^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380644423 10000000000 22866697995591 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415722271/10000000000 : ℝ)^77 ≤ (46110068179051/100000000000000 : ℝ)^61 := by
    have hnat : (5415722271 : ℕ)^77*100000000000000^61 ≤ 46110068179051^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415722271 10000000000 46110068179051 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68652503/500000000 : ℝ)^77 ≤ (163130716331/2000000000000 : ℝ)^61 := by
    have hnat : (68652503 : ℕ)^77*2000000000000^61 ≤ 163130716331^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68652503 500000000 163130716331 2000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380644423/10000000000 : ℝ), (5415722271/10000000000 : ℝ), (68652503/500000000 : ℝ)] ![(22866697995591/50000000000000 : ℝ), (46110068179051/100000000000000 : ℝ), (163130716331/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380644423/10000000000 : ℝ)|^77 ≤ (22866697995591/50000000000000 : ℝ)^61
        have hw : |(5380644423/10000000000 : ℝ)|=(5380644423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415722271/10000000000 : ℝ)|^77 ≤ (46110068179051/100000000000000 : ℝ)^61
        have hw : |(5415722271/10000000000 : ℝ)|=(5415722271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68652503/500000000 : ℝ)|^77 ≤ (163130716331/2000000000000 : ℝ)^61
        have hw : |(68652503/500000000 : ℝ)|=(68652503/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-120889631/1000000000 : ℝ)*x 0 + (5316832693/10000000000 : ℝ)*x 1 + (559126711/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120889631/1000000000 : ℝ)^77 ≤ (6945511154453/100000000000000 : ℝ)^61 := by
    have hnat : (120889631 : ℕ)^77*100000000000000^61 ≤ 6945511154453^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120889631 1000000000 6945511154453 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5316832693/10000000000 : ℝ)^77 ≤ (4504982664093/10000000000000 : ℝ)^61 := by
    have hnat : (5316832693 : ℕ)^77*10000000000000^61 ≤ 4504982664093^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5316832693 10000000000 4504982664093 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559126711/1000000000 : ℝ)^77 ≤ (12001165548449/25000000000000 : ℝ)^61 := by
    have hnat : (559126711 : ℕ)^77*25000000000000^61 ≤ 12001165548449^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559126711 1000000000 12001165548449 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-120889631/1000000000 : ℝ), (5316832693/10000000000 : ℝ), (559126711/1000000000 : ℝ)] ![(6945511154453/100000000000000 : ℝ), (4504982664093/10000000000000 : ℝ), (12001165548449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-120889631/1000000000 : ℝ)|^77 ≤ (6945511154453/100000000000000 : ℝ)^61
        have hw : |(-120889631/1000000000 : ℝ)|=(120889631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5316832693/10000000000 : ℝ)|^77 ≤ (4504982664093/10000000000000 : ℝ)^61
        have hw : |(5316832693/10000000000 : ℝ)|=(5316832693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559126711/1000000000 : ℝ)|^77 ≤ (12001165548449/25000000000000 : ℝ)^61
        have hw : |(559126711/1000000000 : ℝ)|=(559126711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4359460817/10000000000 : ℝ)*x 0 + (-529915087/5000000000 : ℝ)*x 1 + (658841367/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359460817/10000000000 : ℝ)^77 ≤ (35063702241227/100000000000000 : ℝ)^61 := by
    have hnat : (4359460817 : ℕ)^77*100000000000000^61 ≤ 35063702241227^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359460817 10000000000 35063702241227 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529915087/5000000000 : ℝ)^77 ≤ (588248123063/10000000000000 : ℝ)^61 := by
    have hnat : (529915087 : ℕ)^77*10000000000000^61 ≤ 588248123063^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529915087 5000000000 588248123063 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658841367/1000000000 : ℝ)^77 ≤ (59053816515907/100000000000000 : ℝ)^61 := by
    have hnat : (658841367 : ℕ)^77*100000000000000^61 ≤ 59053816515907^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658841367 1000000000 59053816515907 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359460817/10000000000 : ℝ), (-529915087/5000000000 : ℝ), (658841367/1000000000 : ℝ)] ![(35063702241227/100000000000000 : ℝ), (588248123063/10000000000000 : ℝ), (59053816515907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359460817/10000000000 : ℝ)|^77 ≤ (35063702241227/100000000000000 : ℝ)^61
        have hw : |(4359460817/10000000000 : ℝ)|=(4359460817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529915087/5000000000 : ℝ)|^77 ≤ (588248123063/10000000000000 : ℝ)^61
        have hw : |(-529915087/5000000000 : ℝ)|=(529915087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658841367/1000000000 : ℝ)|^77 ≤ (59053816515907/100000000000000 : ℝ)^61
        have hw : |(658841367/1000000000 : ℝ)|=(658841367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5582106253/10000000000 : ℝ)*x 0 + (5327900649/10000000000 : ℝ)*x 1 + (-1206255147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5582106253/10000000000 : ℝ)^77 ≤ (23952700807291/50000000000000 : ℝ)^61 := by
    have hnat : (5582106253 : ℕ)^77*50000000000000^61 ≤ 23952700807291^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5582106253 10000000000 23952700807291 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5327900649/10000000000 : ℝ)^77 ≤ (5646029530751/12500000000000 : ℝ)^61 := by
    have hnat : (5327900649 : ℕ)^77*12500000000000^61 ≤ 5646029530751^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5327900649 10000000000 5646029530751 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206255147/10000000000 : ℝ)^77 ≤ (3463181063233/50000000000000 : ℝ)^61 := by
    have hnat : (1206255147 : ℕ)^77*50000000000000^61 ≤ 3463181063233^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206255147 10000000000 3463181063233 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5582106253/10000000000 : ℝ), (5327900649/10000000000 : ℝ), (-1206255147/10000000000 : ℝ)] ![(23952700807291/50000000000000 : ℝ), (5646029530751/12500000000000 : ℝ), (3463181063233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5582106253/10000000000 : ℝ)|^77 ≤ (23952700807291/50000000000000 : ℝ)^61
        have hw : |(5582106253/10000000000 : ℝ)|=(5582106253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5327900649/10000000000 : ℝ)|^77 ≤ (5646029530751/12500000000000 : ℝ)^61
        have hw : |(5327900649/10000000000 : ℝ)|=(5327900649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1206255147/10000000000 : ℝ)|^77 ≤ (3463181063233/50000000000000 : ℝ)^61
        have hw : |(-1206255147/10000000000 : ℝ)|=(1206255147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7071911377/10000000000 : ℝ)*x 0 + (3564796563/10000000000 : ℝ)*x 1 + (276463609/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7071911377/10000000000 : ℝ)^77 ≤ (64575987288991/100000000000000 : ℝ)^61 := by
    have hnat : (7071911377 : ℕ)^77*100000000000000^61 ≤ 64575987288991^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7071911377 10000000000 64575987288991 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3564796563/10000000000 : ℝ)^77 ≤ (13598959266313/50000000000000 : ℝ)^61 := by
    have hnat : (3564796563 : ℕ)^77*50000000000000^61 ≤ 13598959266313^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3564796563 10000000000 13598959266313 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276463609/2000000000 : ℝ)^77 ≤ (2056523540211/25000000000000 : ℝ)^61 := by
    have hnat : (276463609 : ℕ)^77*25000000000000^61 ≤ 2056523540211^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276463609 2000000000 2056523540211 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7071911377/10000000000 : ℝ), (3564796563/10000000000 : ℝ), (276463609/2000000000 : ℝ)] ![(64575987288991/100000000000000 : ℝ), (13598959266313/50000000000000 : ℝ), (2056523540211/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7071911377/10000000000 : ℝ)|^77 ≤ (64575987288991/100000000000000 : ℝ)^61
        have hw : |(7071911377/10000000000 : ℝ)|=(7071911377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3564796563/10000000000 : ℝ)|^77 ≤ (13598959266313/50000000000000 : ℝ)^61
        have hw : |(3564796563/10000000000 : ℝ)|=(3564796563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276463609/2000000000 : ℝ)|^77 ≤ (2056523540211/25000000000000 : ℝ)^61
        have hw : |(276463609/2000000000 : ℝ)|=(276463609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-38351681/312500000 : ℝ)*x 0 + (6100655197/10000000000 : ℝ)*x 1 + (2387365011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38351681/312500000 : ℝ)^77 ≤ (707890936547/10000000000000 : ℝ)^61 := by
    have hnat : (38351681 : ℕ)^77*10000000000000^61 ≤ 707890936547^61*312500000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38351681 312500000 707890936547 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6100655197/10000000000 : ℝ)^77 ≤ (26794878389191/50000000000000 : ℝ)^61 := by
    have hnat : (6100655197 : ℕ)^77*50000000000000^61 ≤ 26794878389191^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6100655197 10000000000 26794878389191 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2387365011/5000000000 : ℝ)^77 ≤ (9832833457881/25000000000000 : ℝ)^61 := by
    have hnat : (2387365011 : ℕ)^77*25000000000000^61 ≤ 9832833457881^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2387365011 5000000000 9832833457881 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38351681/312500000 : ℝ), (6100655197/10000000000 : ℝ), (2387365011/5000000000 : ℝ)] ![(707890936547/10000000000000 : ℝ), (26794878389191/50000000000000 : ℝ), (9832833457881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38351681/312500000 : ℝ)|^77 ≤ (707890936547/10000000000000 : ℝ)^61
        have hw : |(-38351681/312500000 : ℝ)|=(38351681/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6100655197/10000000000 : ℝ)|^77 ≤ (26794878389191/50000000000000 : ℝ)^61
        have hw : |(6100655197/10000000000 : ℝ)|=(6100655197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2387365011/5000000000 : ℝ)|^77 ≤ (9832833457881/25000000000000 : ℝ)^61
        have hw : |(2387365011/5000000000 : ℝ)|=(2387365011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2785229377/5000000000 : ℝ)*x 0 + (-145020263/2500000000 : ℝ)*x 1 + (5726221323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2785229377/5000000000 : ℝ)^77 ≤ (23889629614973/50000000000000 : ℝ)^61 := by
    have hnat : (2785229377 : ℕ)^77*50000000000000^61 ≤ 23889629614973^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785229377 5000000000 23889629614973 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145020263/2500000000 : ℝ)^77 ≤ (68722325991/2500000000000 : ℝ)^61 := by
    have hnat : (145020263 : ℕ)^77*2500000000000^61 ≤ 68722325991^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145020263 2500000000 68722325991 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5726221323/10000000000 : ℝ)^77 ≤ (49471847721007/100000000000000 : ℝ)^61 := by
    have hnat : (5726221323 : ℕ)^77*100000000000000^61 ≤ 49471847721007^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5726221323 10000000000 49471847721007 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2785229377/5000000000 : ℝ), (-145020263/2500000000 : ℝ), (5726221323/10000000000 : ℝ)] ![(23889629614973/50000000000000 : ℝ), (68722325991/2500000000000 : ℝ), (49471847721007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2785229377/5000000000 : ℝ)|^77 ≤ (23889629614973/50000000000000 : ℝ)^61
        have hw : |(2785229377/5000000000 : ℝ)|=(2785229377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-145020263/2500000000 : ℝ)|^77 ≤ (68722325991/2500000000000 : ℝ)^61
        have hw : |(-145020263/2500000000 : ℝ)|=(145020263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5726221323/10000000000 : ℝ)|^77 ≤ (49471847721007/100000000000000 : ℝ)^61
        have hw : |(5726221323/10000000000 : ℝ)|=(5726221323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4286785187/10000000000 : ℝ)*x 0 + (6219579221/10000000000 : ℝ)*x 1 + (-68403507/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4286785187/10000000000 : ℝ)^77 ≤ (34327460891079/100000000000000 : ℝ)^61 := by
    have hnat : (4286785187 : ℕ)^77*100000000000000^61 ≤ 34327460891079^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286785187 10000000000 34327460891079 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6219579221/10000000000 : ℝ)^77 ≤ (13727945243863/25000000000000 : ℝ)^61 := by
    have hnat : (6219579221 : ℕ)^77*25000000000000^61 ≤ 13727945243863^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6219579221 10000000000 13727945243863 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68403507/400000000 : ℝ)^77 ≤ (10760758115097/100000000000000 : ℝ)^61 := by
    have hnat : (68403507 : ℕ)^77*100000000000000^61 ≤ 10760758115097^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68403507 400000000 10760758115097 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4286785187/10000000000 : ℝ), (6219579221/10000000000 : ℝ), (-68403507/400000000 : ℝ)] ![(34327460891079/100000000000000 : ℝ), (13727945243863/25000000000000 : ℝ), (10760758115097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4286785187/10000000000 : ℝ)|^77 ≤ (34327460891079/100000000000000 : ℝ)^61
        have hw : |(4286785187/10000000000 : ℝ)|=(4286785187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6219579221/10000000000 : ℝ)|^77 ≤ (13727945243863/25000000000000 : ℝ)^61
        have hw : |(6219579221/10000000000 : ℝ)|=(6219579221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68403507/400000000 : ℝ)|^77 ≤ (10760758115097/100000000000000 : ℝ)^61
        have hw : |(-68403507/400000000 : ℝ)|=(68403507/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316055_s2_s2_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3619904831/5000000000 : ℝ)*x 0 + (2618279813/10000000000 : ℝ)*x 1 + (2231808011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3619904831/5000000000 : ℝ)^77 ≤ (8314655932957/12500000000000 : ℝ)^61 := by
    have hnat : (3619904831 : ℕ)^77*12500000000000^61 ≤ 8314655932957^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3619904831 5000000000 8314655932957 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618279813/10000000000 : ℝ)^77 ≤ (18423177287707/100000000000000 : ℝ)^61 := by
    have hnat : (2618279813 : ℕ)^77*100000000000000^61 ≤ 18423177287707^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618279813 10000000000 18423177287707 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231808011/10000000000 : ℝ)^77 ≤ (7529787618323/50000000000000 : ℝ)^61 := by
    have hnat : (2231808011 : ℕ)^77*50000000000000^61 ≤ 7529787618323^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231808011 10000000000 7529787618323 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3619904831/5000000000 : ℝ), (2618279813/10000000000 : ℝ), (2231808011/10000000000 : ℝ)] ![(8314655932957/12500000000000 : ℝ), (18423177287707/100000000000000 : ℝ), (7529787618323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3619904831/5000000000 : ℝ)|^77 ≤ (8314655932957/12500000000000 : ℝ)^61
        have hw : |(3619904831/5000000000 : ℝ)|=(3619904831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618279813/10000000000 : ℝ)|^77 ≤ (18423177287707/100000000000000 : ℝ)^61
        have hw : |(2618279813/10000000000 : ℝ)|=(2618279813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2231808011/10000000000 : ℝ)|^77 ≤ (7529787618323/50000000000000 : ℝ)^61
        have hw : |(2231808011/10000000000 : ℝ)|=(2231808011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316055_s2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((7153/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7153/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56391/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56391/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57007/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57007/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1631/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1631/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33509/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33509/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6587/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6587/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (7153/12500 : ℝ) ^ (19/4 : ℝ) ≤ (7054991700282574653/100000000000000000000 : ℝ) := by
    have hpowers : (7153/12500 : ℝ)^19 ≤ (7054991700282574653/100000000000000000000 : ℝ)^4 := by
      have hnat : (7153 : ℕ)^19*100000000000000000000^4 ≤ 7054991700282574653^4*12500^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7153 12500 7054991700282574653 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7153/12500 : ℝ)) (X := (7054991700282574653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (107054991700282574653/100000000000000000000 : ℝ) ≤ (39627171177853/39062500000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (107054991700282574653/100000000000000000000 : ℝ)^4 ≤ (39627171177853/39062500000000 : ℝ)^19 := by
      have hnat : (107054991700282574653 : ℕ)^4*39062500000000^19 ≤ 39627171177853^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107054991700282574653 100000000000000000000 39627171177853 39062500000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39627171177853/39062500000000 : ℝ)) (X := (107054991700282574653/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (57054991700282574653/50000000000000000000 : ℝ) ≤ (2570443983166761/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (57054991700282574653/50000000000000000000 : ℝ)^4 ≤ (2570443983166761/2500000000000000 : ℝ)^19 := by
      have hnat : (57054991700282574653 : ℕ)^4*2500000000000000^19 ≤ 2570443983166761^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57054991700282574653 50000000000000000000 2570443983166761 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2570443983166761/2500000000000000 : ℝ)) (X := (57054991700282574653/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(564671177853/22353125000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(34305027784169/1430600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (7153/12500 : ℝ)) (alpha := (564671177853/22353125000000 : ℝ)) (beta := (34305027784169/1430600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7153/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(564671177853/22353125000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(34305027784169/1430600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (56391/100000 : ℝ) ^ (19/4 : ℝ) ≤ (6580312694916375953/100000000000000000000 : ℝ) := by
    have hpowers : (56391/100000 : ℝ)^19 ≤ (6580312694916375953/100000000000000000000 : ℝ)^4 := by
      have hnat : (56391 : ℕ)^19*100000000000000000000^4 ≤ 6580312694916375953^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56391 100000 6580312694916375953 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (56391/100000 : ℝ)) (X := (6580312694916375953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (106580312694916375953/100000000000000000000 : ℝ) ≤ (10135069583847561/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (106580312694916375953/100000000000000000000 : ℝ)^4 ≤ (10135069583847561/10000000000000000 : ℝ)^19 := by
      have hnat : (106580312694916375953 : ℕ)^4*10000000000000000^19 ≤ 10135069583847561^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106580312694916375953 100000000000000000000 10135069583847561 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10135069583847561/10000000000000000 : ℝ)) (X := (106580312694916375953/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (56580312694916375953/50000000000000000000 : ℝ) ≤ (10263707856168889/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (56580312694916375953/50000000000000000000 : ℝ)^4 ≤ (10263707856168889/10000000000000000 : ℝ)^19 := by
      have hnat : (56580312694916375953 : ℕ)^4*10000000000000000^19 ≤ 10263707856168889^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56580312694916375953 50000000000000000000 10263707856168889 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10263707856168889/10000000000000000 : ℝ)) (X := (56580312694916375953/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(135069583847561/5639100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(8039892020083/352443750000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (56391/100000 : ℝ)) (alpha := (135069583847561/5639100000000000 : ℝ)) (beta := (8039892020083/352443750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (56391/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(135069583847561/5639100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(8039892020083/352443750000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (57007/100000 : ℝ) ^ (19/4 : ℝ) ≤ (6928813748427009669/100000000000000000000 : ℝ) := by
    have hpowers : (57007/100000 : ℝ)^19 ≤ (6928813748427009669/100000000000000000000 : ℝ)^4 := by
      have hnat : (57007 : ℕ)^19*100000000000000000000^4 ≤ 6928813748427009669^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57007 100000 6928813748427009669 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57007/100000 : ℝ)) (X := (6928813748427009669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (106928813748427009669/100000000000000000000 : ℝ) ≤ (2028407491940773/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (106928813748427009669/100000000000000000000 : ℝ)^4 ≤ (2028407491940773/2000000000000000 : ℝ)^19 := by
      have hnat : (106928813748427009669 : ℕ)^4*2000000000000000^19 ≤ 2028407491940773^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106928813748427009669 100000000000000000000 2028407491940773 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2028407491940773/2000000000000000 : ℝ)) (X := (106928813748427009669/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (56928813748427009669/50000000000000000000 : ℝ) ≤ (5138492369024957/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (56928813748427009669/50000000000000000000 : ℝ)^4 ≤ (5138492369024957/5000000000000000 : ℝ)^19 := by
      have hnat : (56928813748427009669 : ℕ)^4*5000000000000000^19 ≤ 5138492369024957^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56928813748427009669 50000000000000000000 5138492369024957 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5138492369024957/5000000000000000 : ℝ)) (X := (56928813748427009669/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(28407491940773/1140140000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(134947278346049/5700700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (57007/100000 : ℝ)) (alpha := (28407491940773/1140140000000000 : ℝ)) (beta := (134947278346049/5700700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (57007/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(28407491940773/1140140000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(134947278346049/5700700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2025414961/10000000000 : ℝ)*X 0 0+(5563913829/10000000000 : ℝ)*X 0 1+(1184942339/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((947435561/2000000000 : ℝ)*X 1 0+(-1189609257/10000000000 : ℝ)*X 1 1+(385023461/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4730502403/10000000000 : ℝ)*X 2 0+(1393731411/2500000000 : ℝ)*X 2 1+(-1011317963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3023978379/5000000000 : ℝ)*X 0 0+(3910825359/10000000000 : ℝ)*X 0 1+(119515647/500000000 : ℝ)*X 0 2+(3023978379/5000000000 : ℝ)*X 1 0+(3910825359/10000000000 : ℝ)*X 1 1+(119515647/500000000 : ℝ)*X 1 2+(3023978379/5000000000 : ℝ)*X 2 0+(3910825359/10000000000 : ℝ)*X 2 1+(119515647/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-886871247/5000000000 : ℝ)*X 0 0+(5001524747/10000000000 : ℝ)*X 0 1+(220035001/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((928280779/2000000000 : ℝ)*X 1 0+(-614253557/10000000000 : ℝ)*X 1 1+(1648013777/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2317347161/5000000000 : ℝ)*X 2 0+(1546352579/2500000000 : ℝ)*X 2 1+(-129664747/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((5380644423/10000000000 : ℝ)*X 0 0+(5415722271/10000000000 : ℝ)*X 0 1+(68652503/500000000 : ℝ)*X 0 2+(5380644423/10000000000 : ℝ)*X 1 0+(5415722271/10000000000 : ℝ)*X 1 1+(68652503/500000000 : ℝ)*X 1 2+(5380644423/10000000000 : ℝ)*X 2 0+(5415722271/10000000000 : ℝ)*X 2 1+(68652503/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-120889631/1000000000 : ℝ)*X 0 0+(5316832693/10000000000 : ℝ)*X 0 1+(559126711/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4359460817/10000000000 : ℝ)*X 1 0+(-529915087/5000000000 : ℝ)*X 1 1+(658841367/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5582106253/10000000000 : ℝ)*X 2 0+(5327900649/10000000000 : ℝ)*X 2 1+(-1206255147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7071911377/10000000000 : ℝ)*X 0 0+(3564796563/10000000000 : ℝ)*X 0 1+(276463609/2000000000 : ℝ)*X 0 2+(7071911377/10000000000 : ℝ)*X 1 0+(3564796563/10000000000 : ℝ)*X 1 1+(276463609/2000000000 : ℝ)*X 1 2+(7071911377/10000000000 : ℝ)*X 2 0+(3564796563/10000000000 : ℝ)*X 2 1+(276463609/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-38351681/312500000 : ℝ)*X 0 0+(6100655197/10000000000 : ℝ)*X 0 1+(2387365011/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((2785229377/5000000000 : ℝ)*X 1 0+(-145020263/2500000000 : ℝ)*X 1 1+(5726221323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4286785187/10000000000 : ℝ)*X 2 0+(6219579221/10000000000 : ℝ)*X 2 1+(-68403507/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3619904831/5000000000 : ℝ)*X 0 0+(2618279813/10000000000 : ℝ)*X 0 1+(2231808011/10000000000 : ℝ)*X 0 2+(3619904831/5000000000 : ℝ)*X 1 0+(2618279813/10000000000 : ℝ)*X 1 1+(2231808011/10000000000 : ℝ)*X 1 2+(3619904831/5000000000 : ℝ)*X 2 0+(2618279813/10000000000 : ℝ)*X 2 1+(2231808011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((1631/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1631/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (136150807529038835351800489/13394507237500000000000000000000 : ℝ) := by norm_num
    linear_combination (5758201/1000000000000 : ℝ)*(base19) + (522030411/800000000 : ℝ)*(base49) + (742288264759/125000000000 : ℝ)*(major_s2_0) + (742288264759/125000000000 : ℝ)*(major_s2_1) + (742288264759/125000000000 : ℝ)*(major_s2_2) + (32762763/1000000000000 : ℝ)*(sp_s2_0) + (1747859/1000000000000 : ℝ)*(sp_s2_6) + (4263230895767/500000000000 : ℝ)*(sp_s2_7) + (1065805514393/125000000000 : ℝ)*(sp_s2_8) + (8526370065379/1000000000000 : ℝ)*(sp_s2_9) + (3350109174741/1000000000000 : ℝ)*(sp_s2_13) + (187703/3906250000 : ℝ)*(sp_s2_15) + (3371017/1000000000000 : ℝ)*(sp_s2_21) + (63929967/500000000000 : ℝ)*(sp_s2_23) + (3350110922599/1000000000000 : ℝ)*(f.failure) + (8526497925313/1000000000000 : ℝ)*(f.sum) + (25562756132768397179/80367043425000000000000000000000 : ℝ)*base62 + (629616519130023/1425175000000000000000000000 : ℝ)*base64 + (1572781902071/352443750000000000000000000 : ℝ)*base66 + (6666422147721/570070000000000000000000000 : ℝ)*base69 + (1897475124509741369/5097138387500000000000000000000 : ℝ)*base70 + (68333663568031/178825000000000000000000000 : ℝ)*base73 + (6744079440941/2819550000000000000000000000 : ℝ)*base75 + (22701475853803/178825000000000000000000000 : ℝ)*base77 + (200998820309523401/10084120575000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (69057/100000000000000000 : ℝ)*base86 + (69057/100000000000000000 : ℝ)*base88 + (69057/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33509/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33509/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (81441032748151313993832759/5357802895000000000000000000000 : ℝ) := by norm_num
    linear_combination (2564093/1000000000000 : ℝ)*(base39) + (136507811867/250000000000 : ℝ)*(base49) + (729141/500000000000 : ℝ)*(base60) + (2832603882021/500000000000 : ℝ)*(major_s2_0) + (2832603882021/500000000000 : ℝ)*(major_s2_1) + (2832603882021/500000000000 : ℝ)*(major_s2_2) + (696333/31250000000 : ℝ)*(sp_s2_2) + (56638929/1000000000000 : ℝ)*(sp_s2_7) + (11761303/125000000000 : ℝ)*(sp_s2_8) + (1626862410039/200000000000 : ℝ)*(sp_s2_14) + (81342745987/10000000000 : ℝ)*(sp_s2_15) + (2033586601617/250000000000 : ℝ)*(sp_s2_16) + (3195973998083/1000000000000 : ℝ)*(sp_s2_20) + (67774057/1000000000000 : ℝ)*(sp_s2_27) + (159802088607/50000000000 : ℝ)*(f.failure) + (2033592172281/250000000000 : ℝ)*(f.sum) + (9579493788702492139/53578028950000000000000000000000 : ℝ)*base63 + (752492410935851/2850350000000000000000000000 : ℝ)*base64 + (445482694536259/939850000000000000000000000 : ℝ)*base67 + (88527749939199/285035000000000000000000000 : ℝ)*base69 + (7677835185977137261/20388553550000000000000000000000 : ℝ)*base70 + (121114608780071/715300000000000000000000000 : ℝ)*base72 + (7338728807059/469925000000000000000000000 : ℝ)*base74 + (11092533327863/178825000000000000000000000 : ℝ)*base77 + (2411788026864608877/13445494100000000000000000000000 : ℝ)*base79 + (999/5000000000000000 : ℝ)*base87 + (999/5000000000000000 : ℝ)*base89 + (999/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6587/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6587/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10702345405557818544987/2850350000000000000000000000 : ℝ) := by norm_num
    linear_combination (16893194803/200000000000 : ℝ)*(base40) + (574392525857/1000000000000 : ℝ)*(base49) + (35019/500000000000 : ℝ)*(base59) + (2727001656073/500000000000 : ℝ)*(major_s2_0) + (2727001656073/500000000000 : ℝ)*(major_s2_1) + (2727001656073/500000000000 : ℝ)*(major_s2_2) + (63652689/1000000000000 : ℝ)*(sp_s2_0) + (57865679/1000000000000 : ℝ)*(sp_s2_1) + (5394199/1000000000000 : ℝ)*(sp_s2_6) + (22582591/500000000000 : ℝ)*(sp_s2_20) + (7831051491623/1000000000000 : ℝ)*(sp_s2_21) + (978882159829/125000000000 : ℝ)*(sp_s2_22) + (7831115144311/1000000000000 : ℝ)*(sp_s2_23) + (1538419834507/500000000000 : ℝ)*(sp_s2_27) + (615378045679/200000000000 : ℝ)*(f.failure) + (7831115144311/1000000000000 : ℝ)*(f.sum) + (4319442706583674249/160734086850000000000000000000000 : ℝ)*base62 + (735574625415729/1425175000000000000000000000 : ℝ)*base64 + (327033908069893/1409775000000000000000000000 : ℝ)*base67 + (304806973883/1140140000000000000000000 : ℝ)*base69 + (2036303825197324773/20388553550000000000000000000000 : ℝ)*base70 + (89140802087017/715300000000000000000000000 : ℝ)*base73 + (376033538502799/1409775000000000000000000000 : ℝ)*base75 + (60313063338827/89412500000000000000000000 : ℝ)*base77 + (2627365278212759267/40336482300000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (2503/20000000000000000 : ℝ)*base87 + (2503/20000000000000000 : ℝ)*base89 + (2503/20000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((7153/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7153/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56391/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56391/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57007/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57007/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1631/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1631/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33509/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33509/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6587/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6587/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316055_s2 p hpa hpb X hX hprev1

#print axioms solution

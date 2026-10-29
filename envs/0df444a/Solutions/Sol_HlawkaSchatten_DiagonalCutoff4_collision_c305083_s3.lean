-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305083_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:34:07.237712+00:00
-- url     : https://prove2.me/submissions/ae3273b4-9959-42a7-ac99-3f5647e11c3c

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
theorem collision_support_c305083_s3_s3_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1433362757/5000000000 : ℝ)*x 0 + (38864459/80000000 : ℝ)*x 1 + (2578441987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1433362757/5000000000 : ℝ)^67 ≤ (19371100913947/100000000000000 : ℝ)^51 := by
    have hnat : (1433362757 : ℕ)^67*100000000000000^51 ≤ 19371100913947^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1433362757 5000000000 19371100913947 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38864459/80000000 : ℝ)^67 ≤ (1549380083003/4000000000000 : ℝ)^51 := by
    have hnat : (38864459 : ℕ)^67*4000000000000^51 ≤ 1549380083003^51*80000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38864459 80000000 1549380083003 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2578441987/5000000000 : ℝ)^67 ≤ (8378879399221/20000000000000 : ℝ)^51 := by
    have hnat : (2578441987 : ℕ)^67*20000000000000^51 ≤ 8378879399221^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578441987 5000000000 8378879399221 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1433362757/5000000000 : ℝ), (38864459/80000000 : ℝ), (2578441987/5000000000 : ℝ)] ![(19371100913947/100000000000000 : ℝ), (1549380083003/4000000000000 : ℝ), (8378879399221/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1433362757/5000000000 : ℝ)|^67 ≤ (19371100913947/100000000000000 : ℝ)^51
        have hw : |(-1433362757/5000000000 : ℝ)|=(1433362757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38864459/80000000 : ℝ)|^67 ≤ (1549380083003/4000000000000 : ℝ)^51
        have hw : |(38864459/80000000 : ℝ)|=(38864459/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2578441987/5000000000 : ℝ)|^67 ≤ (8378879399221/20000000000000 : ℝ)^51
        have hw : |(2578441987/5000000000 : ℝ)|=(2578441987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6372952627/10000000000 : ℝ)*x 0 + (-1752494947/10000000000 : ℝ)*x 1 + (4450483173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6372952627/10000000000 : ℝ)^67 ≤ (13832395119561/25000000000000 : ℝ)^51 := by
    have hnat : (6372952627 : ℕ)^67*25000000000000^51 ≤ 13832395119561^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6372952627 10000000000 13832395119561 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1752494947/10000000000 : ℝ)^67 ≤ (5073908481711/50000000000000 : ℝ)^51 := by
    have hnat : (1752494947 : ℕ)^67*50000000000000^51 ≤ 5073908481711^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752494947 10000000000 5073908481711 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4450483173/10000000000 : ℝ)^67 ≤ (17261301272461/50000000000000 : ℝ)^51 := by
    have hnat : (4450483173 : ℕ)^67*50000000000000^51 ≤ 17261301272461^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450483173 10000000000 17261301272461 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6372952627/10000000000 : ℝ), (-1752494947/10000000000 : ℝ), (4450483173/10000000000 : ℝ)] ![(13832395119561/25000000000000 : ℝ), (5073908481711/50000000000000 : ℝ), (17261301272461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6372952627/10000000000 : ℝ)|^67 ≤ (13832395119561/25000000000000 : ℝ)^51
        have hw : |(6372952627/10000000000 : ℝ)|=(6372952627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1752494947/10000000000 : ℝ)|^67 ≤ (5073908481711/50000000000000 : ℝ)^51
        have hw : |(-1752494947/10000000000 : ℝ)|=(1752494947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4450483173/10000000000 : ℝ)|^67 ≤ (17261301272461/50000000000000 : ℝ)^51
        have hw : |(4450483173/10000000000 : ℝ)|=(4450483173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1984350491/5000000000 : ℝ)*x 0 + (5980546507/10000000000 : ℝ)*x 1 + (-2870402759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984350491/5000000000 : ℝ)^67 ≤ (29698474683341/100000000000000 : ℝ)^51 := by
    have hnat : (1984350491 : ℕ)^67*100000000000000^51 ≤ 29698474683341^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984350491 5000000000 29698474683341 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5980546507/10000000000 : ℝ)^67 ≤ (12724443605019/25000000000000 : ℝ)^51 := by
    have hnat : (5980546507 : ℕ)^67*25000000000000^51 ≤ 12724443605019^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5980546507 10000000000 12724443605019 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2870402759/10000000000 : ℝ)^67 ≤ (19403750880143/100000000000000 : ℝ)^51 := by
    have hnat : (2870402759 : ℕ)^67*100000000000000^51 ≤ 19403750880143^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2870402759 10000000000 19403750880143 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1984350491/5000000000 : ℝ), (5980546507/10000000000 : ℝ), (-2870402759/10000000000 : ℝ)] ![(29698474683341/100000000000000 : ℝ), (12724443605019/25000000000000 : ℝ), (19403750880143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1984350491/5000000000 : ℝ)|^67 ≤ (29698474683341/100000000000000 : ℝ)^51
        have hw : |(1984350491/5000000000 : ℝ)|=(1984350491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5980546507/10000000000 : ℝ)|^67 ≤ (12724443605019/25000000000000 : ℝ)^51
        have hw : |(5980546507/10000000000 : ℝ)|=(5980546507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2870402759/10000000000 : ℝ)|^67 ≤ (19403750880143/100000000000000 : ℝ)^51
        have hw : |(-2870402759/10000000000 : ℝ)|=(2870402759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (678398849/2000000000 : ℝ)*x 0 + (2331429729/5000000000 : ℝ)*x 1 + (4896182657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (678398849/2000000000 : ℝ)^67 ≤ (12081390145659/50000000000000 : ℝ)^51 := by
    have hnat : (678398849 : ℕ)^67*50000000000000^51 ≤ 12081390145659^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678398849 2000000000 12081390145659 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2331429729/5000000000 : ℝ)^67 ≤ (36702877495279/100000000000000 : ℝ)^51 := by
    have hnat : (2331429729 : ℕ)^67*100000000000000^51 ≤ 36702877495279^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331429729 5000000000 36702877495279 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4896182657/10000000000 : ℝ)^67 ≤ (39134342201831/100000000000000 : ℝ)^51 := by
    have hnat : (4896182657 : ℕ)^67*100000000000000^51 ≤ 39134342201831^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4896182657 10000000000 39134342201831 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(678398849/2000000000 : ℝ), (2331429729/5000000000 : ℝ), (4896182657/10000000000 : ℝ)] ![(12081390145659/50000000000000 : ℝ), (36702877495279/100000000000000 : ℝ), (39134342201831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(678398849/2000000000 : ℝ)|^67 ≤ (12081390145659/50000000000000 : ℝ)^51
        have hw : |(678398849/2000000000 : ℝ)|=(678398849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2331429729/5000000000 : ℝ)|^67 ≤ (36702877495279/100000000000000 : ℝ)^51
        have hw : |(2331429729/5000000000 : ℝ)|=(2331429729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4896182657/10000000000 : ℝ)|^67 ≤ (39134342201831/100000000000000 : ℝ)^51
        have hw : |(4896182657/10000000000 : ℝ)|=(4896182657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-361958397/1250000000 : ℝ)*x 0 + (4848004383/10000000000 : ℝ)*x 1 + (5142630423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361958397/1250000000 : ℝ)^67 ≤ (19628425883341/100000000000000 : ℝ)^51 := by
    have hnat : (361958397 : ℕ)^67*100000000000000^51 ≤ 19628425883341^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361958397 1250000000 19628425883341 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4848004383/10000000000 : ℝ)^67 ≤ (38629234592161/100000000000000 : ℝ)^51 := by
    have hnat : (4848004383 : ℕ)^67*100000000000000^51 ≤ 38629234592161^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4848004383 10000000000 38629234592161 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5142630423/10000000000 : ℝ)^67 ≤ (41742339502141/100000000000000 : ℝ)^51 := by
    have hnat : (5142630423 : ℕ)^67*100000000000000^51 ≤ 41742339502141^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142630423 10000000000 41742339502141 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-361958397/1250000000 : ℝ), (4848004383/10000000000 : ℝ), (5142630423/10000000000 : ℝ)] ![(19628425883341/100000000000000 : ℝ), (38629234592161/100000000000000 : ℝ), (41742339502141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-361958397/1250000000 : ℝ)|^67 ≤ (19628425883341/100000000000000 : ℝ)^51
        have hw : |(-361958397/1250000000 : ℝ)|=(361958397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4848004383/10000000000 : ℝ)|^67 ≤ (38629234592161/100000000000000 : ℝ)^51
        have hw : |(4848004383/10000000000 : ℝ)|=(4848004383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5142630423/10000000000 : ℝ)|^67 ≤ (41742339502141/100000000000000 : ℝ)^51
        have hw : |(5142630423/10000000000 : ℝ)|=(5142630423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (254410837/400000000 : ℝ)*x 0 + (-197829347/1250000000 : ℝ)*x 1 + (4588827861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (254410837/400000000 : ℝ)^67 ≤ (551849821701/1000000000000 : ℝ)^51 := by
    have hnat : (254410837 : ℕ)^67*1000000000000^51 ≤ 551849821701^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254410837 400000000 551849821701 1000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197829347/1250000000 : ℝ)^67 ≤ (8875769668481/100000000000000 : ℝ)^51 := by
    have hnat : (197829347 : ℕ)^67*100000000000000^51 ≤ 8875769668481^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197829347 1250000000 8875769668481 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4588827861/10000000000 : ℝ)^67 ≤ (35939248142551/100000000000000 : ℝ)^51 := by
    have hnat : (4588827861 : ℕ)^67*100000000000000^51 ≤ 35939248142551^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4588827861 10000000000 35939248142551 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(254410837/400000000 : ℝ), (-197829347/1250000000 : ℝ), (4588827861/10000000000 : ℝ)] ![(551849821701/1000000000000 : ℝ), (8875769668481/100000000000000 : ℝ), (35939248142551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(254410837/400000000 : ℝ)|^67 ≤ (551849821701/1000000000000 : ℝ)^51
        have hw : |(254410837/400000000 : ℝ)|=(254410837/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197829347/1250000000 : ℝ)|^67 ≤ (8875769668481/100000000000000 : ℝ)^51
        have hw : |(-197829347/1250000000 : ℝ)|=(197829347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4588827861/10000000000 : ℝ)|^67 ≤ (35939248142551/100000000000000 : ℝ)^51
        have hw : |(4588827861/10000000000 : ℝ)|=(4588827861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3905101691/10000000000 : ℝ)*x 0 + (3071984337/5000000000 : ℝ)*x 1 + (-2732965081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3905101691/10000000000 : ℝ)^67 ≤ (29074818057389/100000000000000 : ℝ)^51 := by
    have hnat : (3905101691 : ℕ)^67*100000000000000^51 ≤ 29074818057389^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3905101691 10000000000 29074818057389 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3071984337/5000000000 : ℝ)^67 ≤ (13183176237333/25000000000000 : ℝ)^51 := by
    have hnat : (3071984337 : ℕ)^67*25000000000000^51 ≤ 13183176237333^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071984337 5000000000 13183176237333 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732965081/10000000000 : ℝ)^67 ≤ (18192476986777/100000000000000 : ℝ)^51 := by
    have hnat : (2732965081 : ℕ)^67*100000000000000^51 ≤ 18192476986777^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732965081 10000000000 18192476986777 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3905101691/10000000000 : ℝ), (3071984337/5000000000 : ℝ), (-2732965081/10000000000 : ℝ)] ![(29074818057389/100000000000000 : ℝ), (13183176237333/25000000000000 : ℝ), (18192476986777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3905101691/10000000000 : ℝ)|^67 ≤ (29074818057389/100000000000000 : ℝ)^51
        have hw : |(3905101691/10000000000 : ℝ)|=(3905101691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3071984337/5000000000 : ℝ)|^67 ≤ (13183176237333/25000000000000 : ℝ)^51
        have hw : |(3071984337/5000000000 : ℝ)|=(3071984337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2732965081/10000000000 : ℝ)|^67 ≤ (18192476986777/100000000000000 : ℝ)^51
        have hw : |(-2732965081/10000000000 : ℝ)|=(2732965081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (414523789/1250000000 : ℝ)*x 0 + (146875437/312500000 : ℝ)*x 1 + (615854769/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414523789/1250000000 : ℝ)^67 ≤ (11727942440363/50000000000000 : ℝ)^51 := by
    have hnat : (414523789 : ℕ)^67*50000000000000^51 ≤ 11727942440363^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414523789 1250000000 11727942440363 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146875437/312500000 : ℝ)^67 ≤ (37087562844013/100000000000000 : ℝ)^51 := by
    have hnat : (146875437 : ℕ)^67*100000000000000^51 ≤ 37087562844013^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146875437 312500000 37087562844013 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (615854769/1250000000 : ℝ)^67 ≤ (2466034516743/6250000000000 : ℝ)^51 := by
    have hnat : (615854769 : ℕ)^67*6250000000000^51 ≤ 2466034516743^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615854769 1250000000 2466034516743 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(414523789/1250000000 : ℝ), (146875437/312500000 : ℝ), (615854769/1250000000 : ℝ)] ![(11727942440363/50000000000000 : ℝ), (37087562844013/100000000000000 : ℝ), (2466034516743/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(414523789/1250000000 : ℝ)|^67 ≤ (11727942440363/50000000000000 : ℝ)^51
        have hw : |(414523789/1250000000 : ℝ)|=(414523789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146875437/312500000 : ℝ)|^67 ≤ (37087562844013/100000000000000 : ℝ)^51
        have hw : |(146875437/312500000 : ℝ)|=(146875437/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(615854769/1250000000 : ℝ)|^67 ≤ (2466034516743/6250000000000 : ℝ)^51
        have hw : |(615854769/1250000000 : ℝ)|=(615854769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-171746763/625000000 : ℝ)*x 0 + (952874961/2000000000 : ℝ)*x 1 + (5345620741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171746763/625000000 : ℝ)^67 ≤ (4580904436661/25000000000000 : ℝ)^51 := by
    have hnat : (171746763 : ℕ)^67*25000000000000^51 ≤ 4580904436661^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171746763 625000000 4580904436661 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (952874961/2000000000 : ℝ)^67 ≤ (37756190489061/100000000000000 : ℝ)^51 := by
    have hnat : (952874961 : ℕ)^67*100000000000000^51 ≤ 37756190489061^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952874961 2000000000 37756190489061 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5345620741/10000000000 : ℝ)^67 ≤ (2745011984561/6250000000000 : ℝ)^51 := by
    have hnat : (5345620741 : ℕ)^67*6250000000000^51 ≤ 2745011984561^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345620741 10000000000 2745011984561 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-171746763/625000000 : ℝ), (952874961/2000000000 : ℝ), (5345620741/10000000000 : ℝ)] ![(4580904436661/25000000000000 : ℝ), (37756190489061/100000000000000 : ℝ), (2745011984561/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-171746763/625000000 : ℝ)|^67 ≤ (4580904436661/25000000000000 : ℝ)^51
        have hw : |(-171746763/625000000 : ℝ)|=(171746763/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(952874961/2000000000 : ℝ)|^67 ≤ (37756190489061/100000000000000 : ℝ)^51
        have hw : |(952874961/2000000000 : ℝ)|=(952874961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5345620741/10000000000 : ℝ)|^67 ≤ (2745011984561/6250000000000 : ℝ)^51
        have hw : |(5345620741/10000000000 : ℝ)|=(5345620741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (203200253/312500000 : ℝ)*x 0 + (-1739707409/10000000000 : ℝ)*x 1 + (4314006417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203200253/312500000 : ℝ)^67 ≤ (14202697925181/25000000000000 : ℝ)^51 := by
    have hnat : (203200253 : ℕ)^67*25000000000000^51 ≤ 14202697925181^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203200253 312500000 14202697925181 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1739707409/10000000000 : ℝ)^67 ≤ (10050652108269/100000000000000 : ℝ)^51 := by
    have hnat : (1739707409 : ℕ)^67*100000000000000^51 ≤ 10050652108269^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739707409 10000000000 10050652108269 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4314006417/10000000000 : ℝ)^67 ≤ (1035579880587/3125000000000 : ℝ)^51 := by
    have hnat : (4314006417 : ℕ)^67*3125000000000^51 ≤ 1035579880587^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314006417 10000000000 1035579880587 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(203200253/312500000 : ℝ), (-1739707409/10000000000 : ℝ), (4314006417/10000000000 : ℝ)] ![(14202697925181/25000000000000 : ℝ), (10050652108269/100000000000000 : ℝ), (1035579880587/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(203200253/312500000 : ℝ)|^67 ≤ (14202697925181/25000000000000 : ℝ)^51
        have hw : |(203200253/312500000 : ℝ)|=(203200253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1739707409/10000000000 : ℝ)|^67 ≤ (10050652108269/100000000000000 : ℝ)^51
        have hw : |(-1739707409/10000000000 : ℝ)|=(1739707409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4314006417/10000000000 : ℝ)|^67 ≤ (1035579880587/3125000000000 : ℝ)^51
        have hw : |(4314006417/10000000000 : ℝ)|=(4314006417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (399232401/1000000000 : ℝ)*x 0 + (1210548817/2000000000 : ℝ)*x 1 + (-275239347/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399232401/1000000000 : ℝ)^67 ≤ (3741365663537/12500000000000 : ℝ)^51 := by
    have hnat : (399232401 : ℕ)^67*12500000000000^51 ≤ 3741365663537^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399232401 1000000000 3741365663537 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1210548817/2000000000 : ℝ)^67 ≤ (5170650627173/10000000000000 : ℝ)^51 := by
    have hnat : (1210548817 : ℕ)^67*10000000000000^51 ≤ 5170650627173^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210548817 2000000000 5170650627173 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275239347/1000000000 : ℝ)^67 ≤ (18362568406373/100000000000000 : ℝ)^51 := by
    have hnat : (275239347 : ℕ)^67*100000000000000^51 ≤ 18362568406373^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275239347 1000000000 18362568406373 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(399232401/1000000000 : ℝ), (1210548817/2000000000 : ℝ), (-275239347/1000000000 : ℝ)] ![(3741365663537/12500000000000 : ℝ), (5170650627173/10000000000000 : ℝ), (18362568406373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(399232401/1000000000 : ℝ)|^67 ≤ (3741365663537/12500000000000 : ℝ)^51
        have hw : |(399232401/1000000000 : ℝ)|=(399232401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1210548817/2000000000 : ℝ)|^67 ≤ (5170650627173/10000000000000 : ℝ)^51
        have hw : |(1210548817/2000000000 : ℝ)|=(1210548817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275239347/1000000000 : ℝ)|^67 ≤ (18362568406373/100000000000000 : ℝ)^51
        have hw : |(-275239347/1000000000 : ℝ)|=(275239347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (664950491/2000000000 : ℝ)*x 0 + (916403539/2000000000 : ℝ)*x 1 + (5034708183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664950491/2000000000 : ℝ)^67 ≤ (5883869486563/25000000000000 : ℝ)^51 := by
    have hnat : (664950491 : ℕ)^67*25000000000000^51 ≤ 5883869486563^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664950491 2000000000 5883869486563 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916403539/2000000000 : ℝ)^67 ≤ (35869194874979/100000000000000 : ℝ)^51 := by
    have hnat : (916403539 : ℕ)^67*100000000000000^51 ≤ 35869194874979^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916403539 2000000000 35869194874979 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5034708183/10000000000 : ℝ)^67 ≤ (20297663577817/50000000000000 : ℝ)^51 := by
    have hnat : (5034708183 : ℕ)^67*50000000000000^51 ≤ 20297663577817^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5034708183 10000000000 20297663577817 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664950491/2000000000 : ℝ), (916403539/2000000000 : ℝ), (5034708183/10000000000 : ℝ)] ![(5883869486563/25000000000000 : ℝ), (35869194874979/100000000000000 : ℝ), (20297663577817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664950491/2000000000 : ℝ)|^67 ≤ (5883869486563/25000000000000 : ℝ)^51
        have hw : |(664950491/2000000000 : ℝ)|=(664950491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916403539/2000000000 : ℝ)|^67 ≤ (35869194874979/100000000000000 : ℝ)^51
        have hw : |(916403539/2000000000 : ℝ)|=(916403539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5034708183/10000000000 : ℝ)|^67 ≤ (20297663577817/50000000000000 : ℝ)^51
        have hw : |(5034708183/10000000000 : ℝ)|=(5034708183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-546240289/2000000000 : ℝ)*x 0 + (623144999/1250000000 : ℝ)*x 1 + (2571751953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546240289/2000000000 : ℝ)^67 ≤ (363541109207/2000000000000 : ℝ)^51 := by
    have hnat : (546240289 : ℕ)^67*2000000000000^51 ≤ 363541109207^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546240289 2000000000 363541109207 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623144999/1250000000 : ℝ)^67 ≤ (40071290460037/100000000000000 : ℝ)^51 := by
    have hnat : (623144999 : ℕ)^67*100000000000000^51 ≤ 40071290460037^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623144999 1250000000 40071290460037 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2571751953/5000000000 : ℝ)^67 ≤ (260947837859/625000000000 : ℝ)^51 := by
    have hnat : (2571751953 : ℕ)^67*625000000000^51 ≤ 260947837859^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571751953 5000000000 260947837859 625000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-546240289/2000000000 : ℝ), (623144999/1250000000 : ℝ), (2571751953/5000000000 : ℝ)] ![(363541109207/2000000000000 : ℝ), (40071290460037/100000000000000 : ℝ), (260947837859/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-546240289/2000000000 : ℝ)|^67 ≤ (363541109207/2000000000000 : ℝ)^51
        have hw : |(-546240289/2000000000 : ℝ)|=(546240289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623144999/1250000000 : ℝ)|^67 ≤ (40071290460037/100000000000000 : ℝ)^51
        have hw : |(623144999/1250000000 : ℝ)|=(623144999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2571751953/5000000000 : ℝ)|^67 ≤ (260947837859/625000000000 : ℝ)^51
        have hw : |(2571751953/5000000000 : ℝ)|=(2571751953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3268794303/5000000000 : ℝ)*x 0 + (-1580741579/10000000000 : ℝ)*x 1 + (219577289/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3268794303/5000000000 : ℝ)^67 ≤ (2860746562167/5000000000000 : ℝ)^51 := by
    have hnat : (3268794303 : ℕ)^67*5000000000000^51 ≤ 2860746562167^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3268794303 5000000000 2860746562167 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1580741579/10000000000 : ℝ)^67 ≤ (8861823842859/100000000000000 : ℝ)^51 := by
    have hnat : (1580741579 : ℕ)^67*100000000000000^51 ≤ 8861823842859^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580741579 10000000000 8861823842859 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219577289/500000000 : ℝ)^67 ≤ (8480811224127/25000000000000 : ℝ)^51 := by
    have hnat : (219577289 : ℕ)^67*25000000000000^51 ≤ 8480811224127^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219577289 500000000 8480811224127 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3268794303/5000000000 : ℝ), (-1580741579/10000000000 : ℝ), (219577289/500000000 : ℝ)] ![(2860746562167/5000000000000 : ℝ), (8861823842859/100000000000000 : ℝ), (8480811224127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3268794303/5000000000 : ℝ)|^67 ≤ (2860746562167/5000000000000 : ℝ)^51
        have hw : |(3268794303/5000000000 : ℝ)|=(3268794303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1580741579/10000000000 : ℝ)|^67 ≤ (8861823842859/100000000000000 : ℝ)^51
        have hw : |(-1580741579/10000000000 : ℝ)|=(1580741579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219577289/500000000 : ℝ)|^67 ≤ (8480811224127/25000000000000 : ℝ)^51
        have hw : |(219577289/500000000 : ℝ)|=(219577289/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3929026883/10000000000 : ℝ)*x 0 + (6004830783/10000000000 : ℝ)*x 1 + (-1441825147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3929026883/10000000000 : ℝ)^67 ≤ (7327264547977/25000000000000 : ℝ)^51 := by
    have hnat : (3929026883 : ℕ)^67*25000000000000^51 ≤ 7327264547977^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3929026883 10000000000 7327264547977 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6004830783/10000000000 : ℝ)^67 ≤ (25584729186053/50000000000000 : ℝ)^51 := by
    have hnat : (6004830783 : ℕ)^67*50000000000000^51 ≤ 25584729186053^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6004830783 10000000000 25584729186053 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1441825147/5000000000 : ℝ)^67 ≤ (19521483421511/100000000000000 : ℝ)^51 := by
    have hnat : (1441825147 : ℕ)^67*100000000000000^51 ≤ 19521483421511^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441825147 5000000000 19521483421511 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3929026883/10000000000 : ℝ), (6004830783/10000000000 : ℝ), (-1441825147/5000000000 : ℝ)] ![(7327264547977/25000000000000 : ℝ), (25584729186053/50000000000000 : ℝ), (19521483421511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3929026883/10000000000 : ℝ)|^67 ≤ (7327264547977/25000000000000 : ℝ)^51
        have hw : |(3929026883/10000000000 : ℝ)|=(3929026883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6004830783/10000000000 : ℝ)|^67 ≤ (25584729186053/50000000000000 : ℝ)^51
        have hw : |(6004830783/10000000000 : ℝ)|=(6004830783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1441825147/5000000000 : ℝ)|^67 ≤ (19521483421511/100000000000000 : ℝ)^51
        have hw : |(-1441825147/5000000000 : ℝ)|=(1441825147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305083_s3_s3_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (854274961/2500000000 : ℝ)*x 0 + (4707994159/10000000000 : ℝ)*x 1 + (4829121319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854274961/2500000000 : ℝ)^67 ≤ (2439799804029/10000000000000 : ℝ)^51 := by
    have hnat : (854274961 : ℕ)^67*10000000000000^51 ≤ 2439799804029^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854274961 2500000000 2439799804029 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4707994159/10000000000 : ℝ)^67 ≤ (18585155830707/50000000000000 : ℝ)^51 := by
    have hnat : (4707994159 : ℕ)^67*50000000000000^51 ≤ 18585155830707^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4707994159 10000000000 18585155830707 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4829121319/10000000000 : ℝ)^67 ≤ (38431690281569/100000000000000 : ℝ)^51 := by
    have hnat : (4829121319 : ℕ)^67*100000000000000^51 ≤ 38431690281569^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829121319 10000000000 38431690281569 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854274961/2500000000 : ℝ), (4707994159/10000000000 : ℝ), (4829121319/10000000000 : ℝ)] ![(2439799804029/10000000000000 : ℝ), (18585155830707/50000000000000 : ℝ), (38431690281569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854274961/2500000000 : ℝ)|^67 ≤ (2439799804029/10000000000000 : ℝ)^51
        have hw : |(854274961/2500000000 : ℝ)|=(854274961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4707994159/10000000000 : ℝ)|^67 ≤ (18585155830707/50000000000000 : ℝ)^51
        have hw : |(4707994159/10000000000 : ℝ)|=(4707994159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4829121319/10000000000 : ℝ)|^67 ≤ (38431690281569/100000000000000 : ℝ)^51
        have hw : |(4829121319/10000000000 : ℝ)|=(4829121319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305083_s3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((41479/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41479/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5139/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5139/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22697/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22697/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12867/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12867/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((919/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(919/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14361/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14361/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (41479/100000 : ℝ) ^ (133/32 : ℝ) ≤ (1289937840961934721/50000000000000000000 : ℝ) := by
    have hpowers : (41479/100000 : ℝ)^133 ≤ (1289937840961934721/50000000000000000000 : ℝ)^32 := by
      have hnat : (41479 : ℕ)^133*50000000000000000000^32 ≤ 1289937840961934721^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41479 100000 1289937840961934721 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41479/100000 : ℝ)) (X := (1289937840961934721/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (51289937840961934721/50000000000000000000 : ℝ) ≤ (1257684148892933/1250000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (51289937840961934721/50000000000000000000 : ℝ)^32 ≤ (1257684148892933/1250000000000000 : ℝ)^133 := by
      have hnat : (51289937840961934721 : ℕ)^32*1250000000000000^133 ≤ 1257684148892933^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51289937840961934721 50000000000000000000 1257684148892933 1250000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257684148892933/1250000000000000 : ℝ)) (X := (51289937840961934721/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (26289937840961934721/25000000000000000000 : ℝ) ≤ (10121783290392427/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (26289937840961934721/25000000000000000000 : ℝ)^32 ≤ (10121783290392427/10000000000000000 : ℝ)^133 := by
      have hnat : (26289937840961934721 : ℕ)^32*10000000000000000^133 ≤ 10121783290392427^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26289937840961934721 25000000000000000000 10121783290392427 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10121783290392427/10000000000000000 : ℝ)) (X := (26289937840961934721/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(7684148892933/518487500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(60310099248963/4147900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (41479/100000 : ℝ)) (alpha := (7684148892933/518487500000000 : ℝ)) (beta := (60310099248963/4147900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (41479/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(7684148892933/518487500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(60310099248963/4147900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (5139/12500 : ℝ) ^ (133/32 : ℝ) ≤ (310789992652136037/12500000000000000000 : ℝ) := by
    have hpowers : (5139/12500 : ℝ)^133 ≤ (310789992652136037/12500000000000000000 : ℝ)^32 := by
      have hnat : (5139 : ℕ)^133*12500000000000000000^32 ≤ 310789992652136037^32*12500^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5139 12500 310789992652136037 12500000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5139/12500 : ℝ)) (X := (310789992652136037/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (12810789992652136037/12500000000000000000 : ℝ) ≤ (5029632291589581/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12810789992652136037/12500000000000000000 : ℝ)^32 ≤ (5029632291589581/5000000000000000 : ℝ)^133 := by
      have hnat : (12810789992652136037 : ℕ)^32*5000000000000000^133 ≤ 5029632291589581^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12810789992652136037 12500000000000000000 5029632291589581 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029632291589581/5000000000000000 : ℝ)) (X := (12810789992652136037/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (6560789992652136037/6250000000000000000 : ℝ) ≤ (5058723592268067/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (6560789992652136037/6250000000000000000 : ℝ)^32 ≤ (5058723592268067/5000000000000000 : ℝ)^133 := by
      have hnat : (6560789992652136037 : ℕ)^32*5000000000000000^133 ≤ 5058723592268067^133*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6560789992652136037 6250000000000000000 5058723592268067 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058723592268067/5000000000000000 : ℝ)) (X := (6560789992652136037/6250000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(29632291589581/2055600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1616183371027/114200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (5139/12500 : ℝ)) (alpha := (29632291589581/2055600000000000 : ℝ)) (beta := (1616183371027/114200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (5139/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(29632291589581/2055600000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1616183371027/114200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (22697/50000 : ℝ) ^ (133/32 : ℝ) ≤ (150127348026093219/4000000000000000000 : ℝ) := by
    have hpowers : (22697/50000 : ℝ)^133 ≤ (150127348026093219/4000000000000000000 : ℝ)^32 := by
      have hnat : (22697 : ℕ)^133*4000000000000000000^32 ≤ 150127348026093219^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22697 50000 150127348026093219 4000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22697/50000 : ℝ)) (X := (150127348026093219/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (4150127348026093219/4000000000000000000 : ℝ) ≤ (5044521448806803/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (4150127348026093219/4000000000000000000 : ℝ)^32 ≤ (5044521448806803/5000000000000000 : ℝ)^133 := by
      have hnat : (4150127348026093219 : ℕ)^32*5000000000000000^133 ≤ 5044521448806803^133*4000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4150127348026093219 4000000000000000000 5044521448806803 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5044521448806803/5000000000000000 : ℝ)) (X := (4150127348026093219/4000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (2150127348026093219/2000000000000000000 : ℝ) ≤ (5087836154409307/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2150127348026093219/2000000000000000000 : ℝ)^32 ≤ (5087836154409307/5000000000000000 : ℝ)^133 := by
      have hnat : (2150127348026093219 : ℕ)^32*5000000000000000^133 ≤ 5087836154409307^133*2000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2150127348026093219 2000000000000000000 5087836154409307 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5087836154409307/5000000000000000 : ℝ)) (X := (2150127348026093219/2000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(44521448806803/2269700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5414338200313/283712500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (22697/50000 : ℝ)) (alpha := (44521448806803/2269700000000000 : ℝ)) (beta := (5414338200313/283712500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (22697/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(44521448806803/2269700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5414338200313/283712500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-1433362757/5000000000 : ℝ)*X 0 0+(38864459/80000000 : ℝ)*X 0 1+(2578441987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((6372952627/10000000000 : ℝ)*X 1 0+(-1752494947/10000000000 : ℝ)*X 1 1+(4450483173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((1984350491/5000000000 : ℝ)*X 2 0+(5980546507/10000000000 : ℝ)*X 2 1+(-2870402759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((678398849/2000000000 : ℝ)*X 0 0+(2331429729/5000000000 : ℝ)*X 0 1+(4896182657/10000000000 : ℝ)*X 0 2+(678398849/2000000000 : ℝ)*X 1 0+(2331429729/5000000000 : ℝ)*X 1 1+(4896182657/10000000000 : ℝ)*X 1 2+(678398849/2000000000 : ℝ)*X 2 0+(2331429729/5000000000 : ℝ)*X 2 1+(4896182657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-361958397/1250000000 : ℝ)*X 0 0+(4848004383/10000000000 : ℝ)*X 0 1+(5142630423/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((254410837/400000000 : ℝ)*X 1 0+(-197829347/1250000000 : ℝ)*X 1 1+(4588827861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((3905101691/10000000000 : ℝ)*X 2 0+(3071984337/5000000000 : ℝ)*X 2 1+(-2732965081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((414523789/1250000000 : ℝ)*X 0 0+(146875437/312500000 : ℝ)*X 0 1+(615854769/1250000000 : ℝ)*X 0 2+(414523789/1250000000 : ℝ)*X 1 0+(146875437/312500000 : ℝ)*X 1 1+(615854769/1250000000 : ℝ)*X 1 2+(414523789/1250000000 : ℝ)*X 2 0+(146875437/312500000 : ℝ)*X 2 1+(615854769/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-171746763/625000000 : ℝ)*X 0 0+(952874961/2000000000 : ℝ)*X 0 1+(5345620741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((203200253/312500000 : ℝ)*X 1 0+(-1739707409/10000000000 : ℝ)*X 1 1+(4314006417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((399232401/1000000000 : ℝ)*X 2 0+(1210548817/2000000000 : ℝ)*X 2 1+(-275239347/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((664950491/2000000000 : ℝ)*X 0 0+(916403539/2000000000 : ℝ)*X 0 1+(5034708183/10000000000 : ℝ)*X 0 2+(664950491/2000000000 : ℝ)*X 1 0+(916403539/2000000000 : ℝ)*X 1 1+(5034708183/10000000000 : ℝ)*X 1 2+(664950491/2000000000 : ℝ)*X 2 0+(916403539/2000000000 : ℝ)*X 2 1+(5034708183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-546240289/2000000000 : ℝ)*X 0 0+(623144999/1250000000 : ℝ)*X 0 1+(2571751953/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((3268794303/5000000000 : ℝ)*X 1 0+(-1580741579/10000000000 : ℝ)*X 1 1+(219577289/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((3929026883/10000000000 : ℝ)*X 2 0+(6004830783/10000000000 : ℝ)*X 2 1+(-1441825147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((854274961/2500000000 : ℝ)*X 0 0+(4707994159/10000000000 : ℝ)*X 0 1+(4829121319/10000000000 : ℝ)*X 0 2+(854274961/2500000000 : ℝ)*X 1 0+(4707994159/10000000000 : ℝ)*X 1 1+(4829121319/10000000000 : ℝ)*X 1 2+(854274961/2500000000 : ℝ)*X 2 0+(4707994159/10000000000 : ℝ)*X 2 1+(4829121319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305083_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((12867/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12867/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (668976400633698508049265949339/80635095115950000000000000000000000 : ℝ) := by norm_num
    linear_combination (103988386079/62500000000 : ℝ)*(base40) + (661655791033/125000000000 : ℝ)*(base49) + (1318179734841/1000000000000 : ℝ)*(base60) + (5570389726399/250000000000 : ℝ)*(major_s3_0) + (5570389726399/250000000000 : ℝ)*(major_s3_1) + (5570389726399/250000000000 : ℝ)*(major_s3_2) + (1362722563/1000000000000 : ℝ)*(sp_s3_0) + (43542861/62500000000 : ℝ)*(sp_s3_1) + (29991753451739/1000000000000 : ℝ)*(sp_s3_7) + (29992451509163/1000000000000 : ℝ)*(sp_s3_8) + (29992555314777/1000000000000 : ℝ)*(sp_s3_9) + (14569966850803/1000000000000 : ℝ)*(sp_s3_13) + (32020637/1000000000000 : ℝ)*(sp_s3_21) + (296440081/500000000000 : ℝ)*(sp_s3_23) + (14569966850803/1000000000000 : ℝ)*(f.failure) + (29993148194939/1000000000000 : ℝ)*(f.sum) + (80720622648678109/323999675000000000000000000000 : ℝ)*base63 + (123138574006769/567425000000000000000000000 : ℝ)*base64 + (20090674058389/513900000000000000000000000 : ℝ)*base67 + (349060546432239/1134850000000000000000000000 : ℝ)*base69 + (3446594295123743991/5884055393750000000000000000000 : ℝ)*base70 + (733137813928909/2073950000000000000000000000 : ℝ)*base73 + (276374849283/7137500000000000000000000 : ℝ)*base75 + (1081509286679/4050683593750000000000000 : ℝ)*base76 + (6174922185588466363/21316058100000000000000000000000 : ℝ)*base79 + (37/3125000000000000 : ℝ)*base87 + (37/3125000000000000 : ℝ)*base89 + (37/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((919/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(919/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4341335061296154764761102836251/322540380463800000000000000000000000 : ℝ) := by norm_num
    linear_combination (1521503723369/500000000000 : ℝ)*(base40) + (168012191553/25000000000 : ℝ)*(base49) + (531435146303/250000000000 : ℝ)*(base60) + (29088511820543/1000000000000 : ℝ)*(major_s3_0) + (29088511820543/1000000000000 : ℝ)*(major_s3_1) + (29088511820543/1000000000000 : ℝ)*(major_s3_2) + (68701729/100000000000 : ℝ)*(sp_s3_2) + (77896303/200000000000 : ℝ)*(sp_s3_6) + (19577984421429/500000000000 : ℝ)*(sp_s3_14) + (39155929054209/1000000000000 : ℝ)*(sp_s3_15) + (39154706127003/1000000000000 : ℝ)*(sp_s3_16) + (19020660830097/1000000000000 : ℝ)*(sp_s3_20) + (39788649/1000000000000 : ℝ)*(sp_s3_22) + (115139713/200000000000 : ℝ)*(sp_s3_23) + (4755262577903/250000000000 : ℝ)*(f.failure) + (19577984421429/500000000000 : ℝ)*(f.sum) + (1587873384636160639/2591997400000000000000000000000 : ℝ)*base62 + (1100354757726961/1134850000000000000000000000 : ℝ)*base65 + (1394670384687443/2055600000000000000000000000 : ℝ)*base67 + (705859431778069/2269700000000000000000000000 : ℝ)*base69 + (284500343070338821/47072443150000000000000000000000 : ℝ)*base71 + (4727719110752499/4147900000000000000000000000 : ℝ)*base73 + (21835546761039/114200000000000000000000000 : ℝ)*base75 + (384923654674301/2073950000000000000000000000 : ℝ)*base77 + (55572642984893751521/85264232400000000000000000000000 : ℝ)*base79 + (3127/3125000000000000 : ℝ)*base86 + (3127/3125000000000000 : ℝ)*base88 + (3127/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14361/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14361/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3172849029252368355799166633/516064608742080000000000000000000 : ℝ) := by norm_num
    linear_combination (2320420155111/1000000000000 : ℝ)*(base40) + (534665815871/100000000000 : ℝ)*(base49) + (919889595781/1000000000000 : ℝ)*(base60) + (22896190684081/1000000000000 : ℝ)*(major_s3_0) + (22896190684081/1000000000000 : ℝ)*(major_s3_1) + (22896190684081/1000000000000 : ℝ)*(major_s3_2) + (844633787/1000000000000 : ℝ)*(sp_s3_1) + (632754467/1000000000000 : ℝ)*(sp_s3_2) + (1093885697/1000000000000 : ℝ)*(sp_s3_7) + (20013263/100000000000 : ℝ)*(sp_s3_15) + (616388186637/20000000000 : ℝ)*(sp_s3_21) + (30819458451129/1000000000000 : ℝ)*(sp_s3_22) + (770496761577/25000000000 : ℝ)*(sp_s3_23) + (598875044049/40000000000 : ℝ)*(sp_s3_27) + (598875044049/40000000000 : ℝ)*(f.failure) + (15410251608773/500000000000 : ℝ)*(f.sum) + (38402964573728047/2591997400000000000000000000000 : ℝ)*base63 + (4817994083651/567425000000000000000000000 : ℝ)*base65 + (343835297325299/2055600000000000000000000000 : ℝ)*base66 + (714907803702133/2269700000000000000000000000 : ℝ)*base69 + (6012466965040204497/47072443150000000000000000000000 : ℝ)*base71 + (279937870011763/4147900000000000000000000000 : ℝ)*base73 + (14091968448533/114200000000000000000000000 : ℝ)*base75 + (20239614950653/518487500000000000000000000 : ℝ)*base77 + (25440675575276958593/85264232400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (23/62500000000000 : ℝ)*base87 + (23/62500000000000 : ℝ)*base89 + (23/62500000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((41479/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41479/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5139/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5139/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22697/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22697/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12867/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12867/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((919/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(919/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14361/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14361/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305083_s3 p hpa hpb X hX hprev2

#print axioms solution

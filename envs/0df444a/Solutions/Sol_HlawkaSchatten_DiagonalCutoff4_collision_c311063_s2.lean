-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:02:00.207259+00:00
-- url     : https://prove2.me/submissions/49ac3154-bd09-46b2-a35e-84f34f26458e

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
theorem collision_support_c311063_s2_s2_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-973200577/10000000000 : ℝ)*x 0 + (5543572467/10000000000 : ℝ)*x 1 + (2832575297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (973200577/10000000000 : ℝ)^9 ≤ (5001696288589/100000000000000 : ℝ)^7 := by
    have hnat : (973200577 : ℕ)^9*100000000000000^7 ≤ 5001696288589^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973200577 10000000000 5001696288589 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5543572467/10000000000 : ℝ)^9 ≤ (23418377307877/50000000000000 : ℝ)^7 := by
    have hnat : (5543572467 : ℕ)^9*50000000000000^7 ≤ 23418377307877^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5543572467 10000000000 23418377307877 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2832575297/5000000000 : ℝ)^9 ≤ (48161549085667/100000000000000 : ℝ)^7 := by
    have hnat : (2832575297 : ℕ)^9*100000000000000^7 ≤ 48161549085667^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832575297 5000000000 48161549085667 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-973200577/10000000000 : ℝ), (5543572467/10000000000 : ℝ), (2832575297/5000000000 : ℝ)] ![(5001696288589/100000000000000 : ℝ), (23418377307877/50000000000000 : ℝ), (48161549085667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-973200577/10000000000 : ℝ)|^9 ≤ (5001696288589/100000000000000 : ℝ)^7
        have hw : |(-973200577/10000000000 : ℝ)|=(973200577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5543572467/10000000000 : ℝ)|^9 ≤ (23418377307877/50000000000000 : ℝ)^7
        have hw : |(5543572467/10000000000 : ℝ)|=(5543572467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2832575297/5000000000 : ℝ)|^9 ≤ (48161549085667/100000000000000 : ℝ)^7
        have hw : |(2832575297/5000000000 : ℝ)|=(2832575297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1385905863/2500000000 : ℝ)*x 0 + (-974021921/10000000000 : ℝ)*x 1 + (141615083/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1385905863/2500000000 : ℝ)^9 ≤ (23418654228011/50000000000000 : ℝ)^7 := by
    have hnat : (1385905863 : ℕ)^9*50000000000000^7 ≤ 23418654228011^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385905863 2500000000 23418654228011 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974021921/10000000000 : ℝ)^9 ≤ (5007124251421/100000000000000 : ℝ)^7 := by
    have hnat : (974021921 : ℕ)^9*100000000000000^7 ≤ 5007124251421^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974021921 10000000000 5007124251421 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141615083/250000000 : ℝ)^9 ≤ (3009722955017/6250000000000 : ℝ)^7 := by
    have hnat : (141615083 : ℕ)^9*6250000000000^7 ≤ 3009722955017^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141615083 250000000 3009722955017 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1385905863/2500000000 : ℝ), (-974021921/10000000000 : ℝ), (141615083/250000000 : ℝ)] ![(23418654228011/50000000000000 : ℝ), (5007124251421/100000000000000 : ℝ), (3009722955017/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1385905863/2500000000 : ℝ)|^9 ≤ (23418654228011/50000000000000 : ℝ)^7
        have hw : |(1385905863/2500000000 : ℝ)|=(1385905863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-974021921/10000000000 : ℝ)|^9 ≤ (5007124251421/100000000000000 : ℝ)^7
        have hw : |(-974021921/10000000000 : ℝ)|=(974021921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141615083/250000000 : ℝ)|^9 ≤ (3009722955017/6250000000000 : ℝ)^7
        have hw : |(141615083/250000000 : ℝ)|=(141615083/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1398825507/2500000000 : ℝ)*x 0 + (2823240499/5000000000 : ℝ)*x 1 + (-459234943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1398825507/2500000000 : ℝ)^9 ≤ (47399429596913/100000000000000 : ℝ)^7 := by
    have hnat : (1398825507 : ℕ)^9*100000000000000^7 ≤ 47399429596913^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398825507 2500000000 47399429596913 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2823240499/5000000000 : ℝ)^9 ≤ (4795758030093/10000000000000 : ℝ)^7 := by
    have hnat : (2823240499 : ℕ)^9*10000000000000^7 ≤ 4795758030093^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823240499 5000000000 4795758030093 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459234943/5000000000 : ℝ)^9 ≤ (464299008611/10000000000000 : ℝ)^7 := by
    have hnat : (459234943 : ℕ)^9*10000000000000^7 ≤ 464299008611^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459234943 5000000000 464299008611 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1398825507/2500000000 : ℝ), (2823240499/5000000000 : ℝ), (-459234943/5000000000 : ℝ)] ![(47399429596913/100000000000000 : ℝ), (4795758030093/10000000000000 : ℝ), (464299008611/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1398825507/2500000000 : ℝ)|^9 ≤ (47399429596913/100000000000000 : ℝ)^7
        have hw : |(1398825507/2500000000 : ℝ)|=(1398825507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2823240499/5000000000 : ℝ)|^9 ≤ (4795758030093/10000000000000 : ℝ)^7
        have hw : |(2823240499/5000000000 : ℝ)|=(2823240499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-459234943/5000000000 : ℝ)|^9 ≤ (464299008611/10000000000000 : ℝ)^7
        have hw : |(-459234943/5000000000 : ℝ)|=(459234943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (275112729/625000000 : ℝ)*x 0 + (534961947/1250000000 : ℝ)*x 1 + (4081927081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275112729/625000000 : ℝ)^9 ≤ (4352320525051/12500000000000 : ℝ)^7 := by
    have hnat : (275112729 : ℕ)^9*12500000000000^7 ≤ 4352320525051^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275112729 625000000 4352320525051 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534961947/1250000000 : ℝ)^9 ≤ (33581668598439/100000000000000 : ℝ)^7 := by
    have hnat : (534961947 : ℕ)^9*100000000000000^7 ≤ 33581668598439^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534961947 1250000000 33581668598439 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4081927081/10000000000 : ℝ)^9 ≤ (7899941796341/25000000000000 : ℝ)^7 := by
    have hnat : (4081927081 : ℕ)^9*25000000000000^7 ≤ 7899941796341^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4081927081 10000000000 7899941796341 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275112729/625000000 : ℝ), (534961947/1250000000 : ℝ), (4081927081/10000000000 : ℝ)] ![(4352320525051/12500000000000 : ℝ), (33581668598439/100000000000000 : ℝ), (7899941796341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275112729/625000000 : ℝ)|^9 ≤ (4352320525051/12500000000000 : ℝ)^7
        have hw : |(275112729/625000000 : ℝ)|=(275112729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(534961947/1250000000 : ℝ)|^9 ≤ (33581668598439/100000000000000 : ℝ)^7
        have hw : |(534961947/1250000000 : ℝ)|=(534961947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4081927081/10000000000 : ℝ)|^9 ≤ (7899941796341/25000000000000 : ℝ)^7
        have hw : |(4081927081/10000000000 : ℝ)|=(4081927081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-974311361/10000000000 : ℝ)*x 0 + (124789651/312500000 : ℝ)*x 1 + (7090514219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (974311361/10000000000 : ℝ)^9 ≤ (1252259341621/25000000000000 : ℝ)^7 := by
    have hnat : (974311361 : ℕ)^9*25000000000000^7 ≤ 1252259341621^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974311361 10000000000 1252259341621 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124789651/312500000 : ℝ)^9 ≤ (3840010681649/12500000000000 : ℝ)^7 := by
    have hnat : (124789651 : ℕ)^9*12500000000000^7 ≤ 3840010681649^7*312500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124789651 312500000 3840010681649 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7090514219/10000000000 : ℝ)^9 ≤ (64270877170077/100000000000000 : ℝ)^7 := by
    have hnat : (7090514219 : ℕ)^9*100000000000000^7 ≤ 64270877170077^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7090514219 10000000000 64270877170077 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-974311361/10000000000 : ℝ), (124789651/312500000 : ℝ), (7090514219/10000000000 : ℝ)] ![(1252259341621/25000000000000 : ℝ), (3840010681649/12500000000000 : ℝ), (64270877170077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-974311361/10000000000 : ℝ)|^9 ≤ (1252259341621/25000000000000 : ℝ)^7
        have hw : |(-974311361/10000000000 : ℝ)|=(974311361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124789651/312500000 : ℝ)|^9 ≤ (3840010681649/12500000000000 : ℝ)^7
        have hw : |(124789651/312500000 : ℝ)|=(124789651/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7090514219/10000000000 : ℝ)|^9 ≤ (64270877170077/100000000000000 : ℝ)^7
        have hw : |(7090514219/10000000000 : ℝ)|=(7090514219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2217312061/5000000000 : ℝ)*x 0 + (-91488647/5000000000 : ℝ)*x 1 + (7089918141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2217312061/5000000000 : ℝ)^9 ≤ (878817650393/2500000000000 : ℝ)^7 := by
    have hnat : (2217312061 : ℕ)^9*2500000000000^7 ≤ 878817650393^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217312061 5000000000 878817650393 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91488647/5000000000 : ℝ)^9 ≤ (22787637/3906250000 : ℝ)^7 := by
    have hnat : (91488647 : ℕ)^9*3906250000^7 ≤ 22787637^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91488647 5000000000 22787637 3906250000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7089918141/10000000000 : ℝ)^9 ≤ (2008247827041/3125000000000 : ℝ)^7 := by
    have hnat : (7089918141 : ℕ)^9*3125000000000^7 ≤ 2008247827041^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7089918141 10000000000 2008247827041 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2217312061/5000000000 : ℝ), (-91488647/5000000000 : ℝ), (7089918141/10000000000 : ℝ)] ![(878817650393/2500000000000 : ℝ), (22787637/3906250000 : ℝ), (2008247827041/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2217312061/5000000000 : ℝ)|^9 ≤ (878817650393/2500000000000 : ℝ)^7
        have hw : |(2217312061/5000000000 : ℝ)|=(2217312061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91488647/5000000000 : ℝ)|^9 ≤ (22787637/3906250000 : ℝ)^7
        have hw : |(-91488647/5000000000 : ℝ)|=(91488647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7089918141/10000000000 : ℝ)|^9 ≤ (2008247827041/3125000000000 : ℝ)^7
        have hw : |(7089918141/10000000000 : ℝ)|=(7089918141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1034089757/2500000000 : ℝ)*x 0 + (737994549/1000000000 : ℝ)*x 1 + (-77714591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034089757/2500000000 : ℝ)^9 ≤ (32142568521311/100000000000000 : ℝ)^7 := by
    have hnat : (1034089757 : ℕ)^9*100000000000000^7 ≤ 32142568521311^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034089757 2500000000 32142568521311 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (737994549/1000000000 : ℝ)^9 ≤ (67663437149173/100000000000000 : ℝ)^7 := by
    have hnat : (737994549 : ℕ)^9*100000000000000^7 ≤ 67663437149173^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737994549 1000000000 67663437149173 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77714591/10000000000 : ℝ)^9 ≤ (48498579861/25000000000000 : ℝ)^7 := by
    have hnat : (77714591 : ℕ)^9*25000000000000^7 ≤ 48498579861^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77714591 10000000000 48498579861 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034089757/2500000000 : ℝ), (737994549/1000000000 : ℝ), (-77714591/10000000000 : ℝ)] ![(32142568521311/100000000000000 : ℝ), (67663437149173/100000000000000 : ℝ), (48498579861/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034089757/2500000000 : ℝ)|^9 ≤ (32142568521311/100000000000000 : ℝ)^7
        have hw : |(1034089757/2500000000 : ℝ)|=(1034089757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(737994549/1000000000 : ℝ)|^9 ≤ (67663437149173/100000000000000 : ℝ)^7
        have hw : |(737994549/1000000000 : ℝ)|=(737994549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77714591/10000000000 : ℝ)|^9 ≤ (48498579861/25000000000000 : ℝ)^7
        have hw : |(-77714591/10000000000 : ℝ)|=(77714591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4103836599/10000000000 : ℝ)*x 0 + (6525647797/10000000000 : ℝ)*x 1 + (430513787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4103836599/10000000000 : ℝ)^9 ≤ (31818004188363/100000000000000 : ℝ)^7 := by
    have hnat : (4103836599 : ℕ)^9*100000000000000^7 ≤ 31818004188363^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4103836599 10000000000 31818004188363 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6525647797/10000000000 : ℝ)^9 ≤ (28882112651373/50000000000000 : ℝ)^7 := by
    have hnat : (6525647797 : ℕ)^9*50000000000000^7 ≤ 28882112651373^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6525647797 10000000000 28882112651373 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430513787/2500000000 : ℝ)^9 ≤ (5208885246331/50000000000000 : ℝ)^7 := by
    have hnat : (430513787 : ℕ)^9*50000000000000^7 ≤ 5208885246331^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430513787 2500000000 5208885246331 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4103836599/10000000000 : ℝ), (6525647797/10000000000 : ℝ), (430513787/2500000000 : ℝ)] ![(31818004188363/100000000000000 : ℝ), (28882112651373/50000000000000 : ℝ), (5208885246331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4103836599/10000000000 : ℝ)|^9 ≤ (31818004188363/100000000000000 : ℝ)^7
        have hw : |(4103836599/10000000000 : ℝ)|=(4103836599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6525647797/10000000000 : ℝ)|^9 ≤ (28882112651373/50000000000000 : ℝ)^7
        have hw : |(6525647797/10000000000 : ℝ)|=(6525647797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(430513787/2500000000 : ℝ)|^9 ≤ (5208885246331/50000000000000 : ℝ)^7
        have hw : |(430513787/2500000000 : ℝ)|=(430513787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-168812517/10000000000 : ℝ)*x 0 + (2185548717/5000000000 : ℝ)*x 1 + (17875533/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168812517/10000000000 : ℝ)^9 ≤ (525955292513/100000000000000 : ℝ)^7 := by
    have hnat : (168812517 : ℕ)^9*100000000000000^7 ≤ 525955292513^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168812517 10000000000 525955292513 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185548717/5000000000 : ℝ)^9 ≤ (4313323862591/12500000000000 : ℝ)^7 := by
    have hnat : (2185548717 : ℕ)^9*12500000000000^7 ≤ 4313323862591^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185548717 5000000000 4313323862591 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17875533/25000000 : ℝ)^9 ≤ (16241863447347/25000000000000 : ℝ)^7 := by
    have hnat : (17875533 : ℕ)^9*25000000000000^7 ≤ 16241863447347^7*25000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17875533 25000000 16241863447347 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168812517/10000000000 : ℝ), (2185548717/5000000000 : ℝ), (17875533/25000000 : ℝ)] ![(525955292513/100000000000000 : ℝ), (4313323862591/12500000000000 : ℝ), (16241863447347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168812517/10000000000 : ℝ)|^9 ≤ (525955292513/100000000000000 : ℝ)^7
        have hw : |(-168812517/10000000000 : ℝ)|=(168812517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2185548717/5000000000 : ℝ)|^9 ≤ (4313323862591/12500000000000 : ℝ)^7
        have hw : |(2185548717/5000000000 : ℝ)|=(2185548717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17875533/25000000 : ℝ)|^9 ≤ (16241863447347/25000000000000 : ℝ)^7
        have hw : |(17875533/25000000 : ℝ)|=(17875533/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (977045173/2500000000 : ℝ)*x 0 + (-996856279/10000000000 : ℝ)*x 1 + (3574804423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977045173/2500000000 : ℝ)^9 ≤ (149405286059/500000000000 : ℝ)^7 := by
    have hnat : (977045173 : ℕ)^9*500000000000^7 ≤ 149405286059^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977045173 2500000000 149405286059 500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996856279/10000000000 : ℝ)^9 ≤ (1289637257431/25000000000000 : ℝ)^7 := by
    have hnat : (996856279 : ℕ)^9*25000000000000^7 ≤ 1289637257431^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996856279 10000000000 1289637257431 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3574804423/5000000000 : ℝ)^9 ≤ (64960393744197/100000000000000 : ℝ)^7 := by
    have hnat : (3574804423 : ℕ)^9*100000000000000^7 ≤ 64960393744197^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574804423 5000000000 64960393744197 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(977045173/2500000000 : ℝ), (-996856279/10000000000 : ℝ), (3574804423/5000000000 : ℝ)] ![(149405286059/500000000000 : ℝ), (1289637257431/25000000000000 : ℝ), (64960393744197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(977045173/2500000000 : ℝ)|^9 ≤ (149405286059/500000000000 : ℝ)^7
        have hw : |(977045173/2500000000 : ℝ)|=(977045173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-996856279/10000000000 : ℝ)|^9 ≤ (1289637257431/25000000000000 : ℝ)^7
        have hw : |(-996856279/10000000000 : ℝ)|=(996856279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3574804423/5000000000 : ℝ)|^9 ≤ (64960393744197/100000000000000 : ℝ)^7
        have hw : |(3574804423/5000000000 : ℝ)|=(3574804423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1414256067/2000000000 : ℝ)*x 0 + (140141553/312500000 : ℝ)*x 1 + (-26635851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1414256067/2000000000 : ℝ)^9 ≤ (32023404667341/50000000000000 : ℝ)^7 := by
    have hnat : (1414256067 : ℕ)^9*50000000000000^7 ≤ 32023404667341^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414256067 2000000000 32023404667341 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140141553/312500000 : ℝ)^9 ≤ (35662143914051/100000000000000 : ℝ)^7 := by
    have hnat : (140141553 : ℕ)^9*100000000000000^7 ≤ 35662143914051^7*312500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140141553 312500000 35662143914051 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26635851/2500000000 : ℝ)^9 ≤ (145523367089/50000000000000 : ℝ)^7 := by
    have hnat : (26635851 : ℕ)^9*50000000000000^7 ≤ 145523367089^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26635851 2500000000 145523367089 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1414256067/2000000000 : ℝ), (140141553/312500000 : ℝ), (-26635851/2500000000 : ℝ)] ![(32023404667341/50000000000000 : ℝ), (35662143914051/100000000000000 : ℝ), (145523367089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1414256067/2000000000 : ℝ)|^9 ≤ (32023404667341/50000000000000 : ℝ)^7
        have hw : |(1414256067/2000000000 : ℝ)|=(1414256067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140141553/312500000 : ℝ)|^9 ≤ (35662143914051/100000000000000 : ℝ)^7
        have hw : |(140141553/312500000 : ℝ)|=(140141553/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26635851/2500000000 : ℝ)|^9 ≤ (145523367089/50000000000000 : ℝ)^7
        have hw : |(-26635851/2500000000 : ℝ)|=(26635851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1807692787/2500000000 : ℝ)*x 0 + (163568469/500000000 : ℝ)*x 1 + (1709100683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1807692787/2500000000 : ℝ)^9 ≤ (65910051307511/100000000000000 : ℝ)^7 := by
    have hnat : (1807692787 : ℕ)^9*100000000000000^7 ≤ 65910051307511^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1807692787 2500000000 65910051307511 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163568469/500000000 : ℝ)^9 ≤ (4754566103613/20000000000000 : ℝ)^7 := by
    have hnat : (163568469 : ℕ)^9*20000000000000^7 ≤ 4754566103613^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163568469 500000000 4754566103613 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1709100683/10000000000 : ℝ)^9 ≤ (644819884649/6250000000000 : ℝ)^7 := by
    have hnat : (1709100683 : ℕ)^9*6250000000000^7 ≤ 644819884649^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709100683 10000000000 644819884649 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1807692787/2500000000 : ℝ), (163568469/500000000 : ℝ), (1709100683/10000000000 : ℝ)] ![(65910051307511/100000000000000 : ℝ), (4754566103613/20000000000000 : ℝ), (644819884649/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1807692787/2500000000 : ℝ)|^9 ≤ (65910051307511/100000000000000 : ℝ)^7
        have hw : |(1807692787/2500000000 : ℝ)|=(1807692787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163568469/500000000 : ℝ)|^9 ≤ (4754566103613/20000000000000 : ℝ)^7
        have hw : |(163568469/500000000 : ℝ)|=(163568469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1709100683/10000000000 : ℝ)|^9 ≤ (644819884649/6250000000000 : ℝ)^7
        have hw : |(1709100683/10000000000 : ℝ)|=(1709100683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-6485089/500000000 : ℝ)*x 0 + (3293655327/5000000000 : ℝ)*x 1 + (1253352413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6485089/500000000 : ℝ)^9 ≤ (374789687323/100000000000000 : ℝ)^7 := by
    have hnat : (6485089 : ℕ)^9*100000000000000^7 ≤ 374789687323^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6485089 500000000 374789687323 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3293655327/5000000000 : ℝ)^9 ≤ (14616738618717/25000000000000 : ℝ)^7 := by
    have hnat : (3293655327 : ℕ)^9*25000000000000^7 ≤ 14616738618717^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3293655327 5000000000 14616738618717 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1253352413/2500000000 : ℝ)^9 ≤ (20579127908913/50000000000000 : ℝ)^7 := by
    have hnat : (1253352413 : ℕ)^9*50000000000000^7 ≤ 20579127908913^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253352413 2500000000 20579127908913 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6485089/500000000 : ℝ), (3293655327/5000000000 : ℝ), (1253352413/2500000000 : ℝ)] ![(374789687323/100000000000000 : ℝ), (14616738618717/25000000000000 : ℝ), (20579127908913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6485089/500000000 : ℝ)|^9 ≤ (374789687323/100000000000000 : ℝ)^7
        have hw : |(-6485089/500000000 : ℝ)|=(6485089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3293655327/5000000000 : ℝ)|^9 ≤ (14616738618717/25000000000000 : ℝ)^7
        have hw : |(3293655327/5000000000 : ℝ)|=(3293655327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1253352413/2500000000 : ℝ)|^9 ≤ (20579127908913/50000000000000 : ℝ)^7
        have hw : |(1253352413/2500000000 : ℝ)|=(1253352413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7069674297/10000000000 : ℝ)*x 0 + (-18304663/2000000000 : ℝ)*x 1 + (4491409341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7069674297/10000000000 : ℝ)^9 ≤ (8003513429831/12500000000000 : ℝ)^7 := by
    have hnat : (7069674297 : ℕ)^9*12500000000000^7 ≤ 8003513429831^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7069674297 10000000000 8003513429831 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18304663/2000000000 : ℝ)^9 ≤ (47878687369/20000000000000 : ℝ)^7 := by
    have hnat : (18304663 : ℕ)^9*20000000000000^7 ≤ 47878687369^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18304663 2000000000 47878687369 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491409341/10000000000 : ℝ)^9 ≤ (285859992877/800000000000 : ℝ)^7 := by
    have hnat : (4491409341 : ℕ)^9*800000000000^7 ≤ 285859992877^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491409341 10000000000 285859992877 800000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7069674297/10000000000 : ℝ), (-18304663/2000000000 : ℝ), (4491409341/10000000000 : ℝ)] ![(8003513429831/12500000000000 : ℝ), (47878687369/20000000000000 : ℝ), (285859992877/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7069674297/10000000000 : ℝ)|^9 ≤ (8003513429831/12500000000000 : ℝ)^7
        have hw : |(7069674297/10000000000 : ℝ)|=(7069674297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18304663/2000000000 : ℝ)|^9 ≤ (47878687369/20000000000000 : ℝ)^7
        have hw : |(-18304663/2000000000 : ℝ)|=(18304663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491409341/10000000000 : ℝ)|^9 ≤ (285859992877/800000000000 : ℝ)^7
        have hw : |(4491409341/10000000000 : ℝ)|=(4491409341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (770946321/2000000000 : ℝ)*x 0 + (3611196909/5000000000 : ℝ)*x 1 + (-473668227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (770946321/2000000000 : ℝ)^9 ≤ (29356667732467/100000000000000 : ℝ)^7 := by
    have hnat : (770946321 : ℕ)^9*100000000000000^7 ≤ 29356667732467^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770946321 2000000000 29356667732467 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3611196909/5000000000 : ℝ)^9 ≤ (1645297222391/2500000000000 : ℝ)^7 := by
    have hnat : (3611196909 : ℕ)^9*2500000000000^7 ≤ 1645297222391^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3611196909 5000000000 1645297222391 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (473668227/5000000000 : ℝ)^9 ≤ (2415721677987/50000000000000 : ℝ)^7 := by
    have hnat : (473668227 : ℕ)^9*50000000000000^7 ≤ 2415721677987^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473668227 5000000000 2415721677987 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(770946321/2000000000 : ℝ), (3611196909/5000000000 : ℝ), (-473668227/5000000000 : ℝ)] ![(29356667732467/100000000000000 : ℝ), (1645297222391/2500000000000 : ℝ), (2415721677987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(770946321/2000000000 : ℝ)|^9 ≤ (29356667732467/100000000000000 : ℝ)^7
        have hw : |(770946321/2000000000 : ℝ)|=(770946321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3611196909/5000000000 : ℝ)|^9 ≤ (1645297222391/2500000000000 : ℝ)^7
        have hw : |(3611196909/5000000000 : ℝ)|=(3611196909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-473668227/5000000000 : ℝ)|^9 ≤ (2415721677987/50000000000000 : ℝ)^7
        have hw : |(-473668227/5000000000 : ℝ)|=(473668227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311063_s2_s2_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1477094187/2000000000 : ℝ)*x 0 + (2601729741/10000000000 : ℝ)*x 1 + (2234505837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1477094187/2000000000 : ℝ)^9 ≤ (67728578846709/100000000000000 : ℝ)^7 := by
    have hnat : (1477094187 : ℕ)^9*100000000000000^7 ≤ 67728578846709^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477094187 2000000000 67728578846709 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2601729741/10000000000 : ℝ)^9 ≤ (8854503984393/50000000000000 : ℝ)^7 := by
    have hnat : (2601729741 : ℕ)^9*50000000000000^7 ≤ 8854503984393^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601729741 10000000000 8854503984393 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234505837/10000000000 : ℝ)^9 ≤ (14562413166439/100000000000000 : ℝ)^7 := by
    have hnat : (2234505837 : ℕ)^9*100000000000000^7 ≤ 14562413166439^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234505837 10000000000 14562413166439 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1477094187/2000000000 : ℝ), (2601729741/10000000000 : ℝ), (2234505837/10000000000 : ℝ)] ![(67728578846709/100000000000000 : ℝ), (8854503984393/50000000000000 : ℝ), (14562413166439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1477094187/2000000000 : ℝ)|^9 ≤ (67728578846709/100000000000000 : ℝ)^7
        have hw : |(1477094187/2000000000 : ℝ)|=(1477094187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2601729741/10000000000 : ℝ)|^9 ≤ (8854503984393/50000000000000 : ℝ)^7
        have hw : |(2601729741/10000000000 : ℝ)|=(2601729741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2234505837/10000000000 : ℝ)|^9 ≤ (14562413166439/100000000000000 : ℝ)^7
        have hw : |(2234505837/10000000000 : ℝ)|=(2234505837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311063_s2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((72293/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72293/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(72331/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6971/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6971/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((28879/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28879/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29233/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29233/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28023/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28023/50000 : ℝ)*X 1 2) := by
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
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (89829/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (72293/100000 : ℝ) ^ (71/16 : ℝ) ≤ (23699522602009708113/100000000000000000000 : ℝ) := by
    have hpowers : (72293/100000 : ℝ)^71 ≤ (23699522602009708113/100000000000000000000 : ℝ)^16 := by
      have hnat : (72293 : ℕ)^71*100000000000000000000^16 ≤ 23699522602009708113^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72293 100000 23699522602009708113 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72293/100000 : ℝ)) (X := (23699522602009708113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (123699522602009708113/100000000000000000000 : ℝ) ≤ (10490962369690687/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (123699522602009708113/100000000000000000000 : ℝ)^16 ≤ (10490962369690687/10000000000000000 : ℝ)^71 := by
      have hnat : (123699522602009708113 : ℕ)^16*10000000000000000^71 ≤ 10490962369690687^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123699522602009708113 100000000000000000000 10490962369690687 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10490962369690687/10000000000000000 : ℝ)) (X := (123699522602009708113/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (73699522602009708113/50000000000000000000 : ℝ) ≤ (545683264013593/500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (73699522602009708113/50000000000000000000 : ℝ)^16 ≤ (545683264013593/500000000000000 : ℝ)^71 := by
      have hnat : (73699522602009708113 : ℕ)^16*500000000000000^71 ≤ 545683264013593^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73699522602009708113 50000000000000000000 545683264013593 500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (545683264013593/500000000000000 : ℝ)) (X := (73699522602009708113/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(490962369690687/7229300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(422702910581173/7229300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (72293/100000 : ℝ)) (alpha := (490962369690687/7229300000000000 : ℝ)) (beta := (422702910581173/7229300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (72293/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(490962369690687/7229300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(422702910581173/7229300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (72331/100000 : ℝ) ^ (71/16 : ℝ) ≤ (11877426109446813569/50000000000000000000 : ℝ) := by
    have hpowers : (72331/100000 : ℝ)^71 ≤ (11877426109446813569/50000000000000000000 : ℝ)^16 := by
      have hnat : (72331 : ℕ)^71*50000000000000000000^16 ≤ 11877426109446813569^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72331 100000 11877426109446813569 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72331/100000 : ℝ)) (X := (11877426109446813569/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (61877426109446813569/50000000000000000000 : ℝ) ≤ (10492019652999651/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (61877426109446813569/50000000000000000000 : ℝ)^16 ≤ (10492019652999651/10000000000000000 : ℝ)^71 := by
      have hnat : (61877426109446813569 : ℕ)^16*10000000000000000^71 ≤ 10492019652999651^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61877426109446813569 50000000000000000000 10492019652999651 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10492019652999651/10000000000000000 : ℝ)) (X := (61877426109446813569/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (36877426109446813569/25000000000000000000 : ℝ) ≤ (2728877785329681/2500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (36877426109446813569/25000000000000000000 : ℝ)^16 ≤ (2728877785329681/2500000000000000 : ℝ)^71 := by
      have hnat : (36877426109446813569 : ℕ)^16*2500000000000000^71 ≤ 2728877785329681^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36877426109446813569 25000000000000000000 2728877785329681 2500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2728877785329681/2500000000000000 : ℝ)) (X := (36877426109446813569/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(70288521857093/1033300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(423491488319073/7233100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (72331/100000 : ℝ)) (alpha := (70288521857093/1033300000000000 : ℝ)) (beta := (423491488319073/7233100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (72331/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(70288521857093/1033300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(423491488319073/7233100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (6971/10000 : ℝ) ^ (71/16 : ℝ) ≤ (5041525153208577337/25000000000000000000 : ℝ) := by
    have hpowers : (6971/10000 : ℝ)^71 ≤ (5041525153208577337/25000000000000000000 : ℝ)^16 := by
      have hnat : (6971 : ℕ)^71*25000000000000000000^16 ≤ 5041525153208577337^16*10000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6971 10000 5041525153208577337 25000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6971/10000 : ℝ)) (X := (5041525153208577337/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (30041525153208577337/25000000000000000000 : ℝ) ≤ (208453422898843/200000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (30041525153208577337/25000000000000000000 : ℝ)^16 ≤ (208453422898843/200000000000000 : ℝ)^71 := by
      have hnat : (30041525153208577337 : ℕ)^16*200000000000000^71 ≤ 208453422898843^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30041525153208577337 25000000000000000000 208453422898843 200000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (208453422898843/200000000000000 : ℝ)) (X := (30041525153208577337/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (17541525153208577337/12500000000000000000 : ℝ) ≤ (43173992151137/40000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (17541525153208577337/12500000000000000000 : ℝ)^16 ≤ (43173992151137/40000000000000 : ℝ)^71 := by
      have hnat : (17541525153208577337 : ℕ)^16*40000000000000^71 ≤ 43173992151137^71*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17541525153208577337 12500000000000000000 43173992151137 40000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (43173992151137/40000000000000 : ℝ)) (X := (17541525153208577337/12500000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(8453422898843/139420000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(3708268928421/69710000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (6971/10000 : ℝ)) (alpha := (8453422898843/139420000000000 : ℝ)) (beta := (3708268928421/69710000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6971/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(8453422898843/139420000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(3708268928421/69710000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-973200577/10000000000 : ℝ)*X 0 0+(5543572467/10000000000 : ℝ)*X 0 1+(2832575297/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1385905863/2500000000 : ℝ)*X 1 0+(-974021921/10000000000 : ℝ)*X 1 1+(141615083/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1398825507/2500000000 : ℝ)*X 2 0+(2823240499/5000000000 : ℝ)*X 2 1+(-459234943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((275112729/625000000 : ℝ)*X 0 0+(534961947/1250000000 : ℝ)*X 0 1+(4081927081/10000000000 : ℝ)*X 0 2+(275112729/625000000 : ℝ)*X 1 0+(534961947/1250000000 : ℝ)*X 1 1+(4081927081/10000000000 : ℝ)*X 1 2+(275112729/625000000 : ℝ)*X 2 0+(534961947/1250000000 : ℝ)*X 2 1+(4081927081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-974311361/10000000000 : ℝ)*X 0 0+(124789651/312500000 : ℝ)*X 0 1+(7090514219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2217312061/5000000000 : ℝ)*X 1 0+(-91488647/5000000000 : ℝ)*X 1 1+(7089918141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1034089757/2500000000 : ℝ)*X 2 0+(737994549/1000000000 : ℝ)*X 2 1+(-77714591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((4103836599/10000000000 : ℝ)*X 0 0+(6525647797/10000000000 : ℝ)*X 0 1+(430513787/2500000000 : ℝ)*X 0 2+(4103836599/10000000000 : ℝ)*X 1 0+(6525647797/10000000000 : ℝ)*X 1 1+(430513787/2500000000 : ℝ)*X 1 2+(4103836599/10000000000 : ℝ)*X 2 0+(6525647797/10000000000 : ℝ)*X 2 1+(430513787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-168812517/10000000000 : ℝ)*X 0 0+(2185548717/5000000000 : ℝ)*X 0 1+(17875533/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((977045173/2500000000 : ℝ)*X 1 0+(-996856279/10000000000 : ℝ)*X 1 1+(3574804423/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1414256067/2000000000 : ℝ)*X 2 0+(140141553/312500000 : ℝ)*X 2 1+(-26635851/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1807692787/2500000000 : ℝ)*X 0 0+(163568469/500000000 : ℝ)*X 0 1+(1709100683/10000000000 : ℝ)*X 0 2+(1807692787/2500000000 : ℝ)*X 1 0+(163568469/500000000 : ℝ)*X 1 1+(1709100683/10000000000 : ℝ)*X 1 2+(1807692787/2500000000 : ℝ)*X 2 0+(163568469/500000000 : ℝ)*X 2 1+(1709100683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-6485089/500000000 : ℝ)*X 0 0+(3293655327/5000000000 : ℝ)*X 0 1+(1253352413/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((7069674297/10000000000 : ℝ)*X 1 0+(-18304663/2000000000 : ℝ)*X 1 1+(4491409341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((770946321/2000000000 : ℝ)*X 2 0+(3611196909/5000000000 : ℝ)*X 2 1+(-473668227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1477094187/2000000000 : ℝ)*X 0 0+(2601729741/10000000000 : ℝ)*X 0 1+(2234505837/10000000000 : ℝ)*X 0 2+(1477094187/2000000000 : ℝ)*X 1 0+(2601729741/10000000000 : ℝ)*X 1 1+(2234505837/10000000000 : ℝ)*X 1 2+(1477094187/2000000000 : ℝ)*X 2 0+(2601729741/10000000000 : ℝ)*X 2 1+(2234505837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((28879/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28879/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18868556052609872490400865271/1458061326259720000000000000000000 : ℝ) := by norm_num
    linear_combination (84959507493/250000000000 : ℝ)*(base7) + (594793/500000000000 : ℝ)*(base50) + (30353267521/250000000000 : ℝ)*(base60) + (2607253779567/1000000000000 : ℝ)*(major_s2_0) + (2607253779567/1000000000000 : ℝ)*(major_s2_1) + (2607253779567/1000000000000 : ℝ)*(major_s2_2) + (5823139/500000000000 : ℝ)*(sp_s2_0) + (2278983/1000000000000 : ℝ)*(sp_s2_6) + (856117372633/250000000000 : ℝ)*(sp_s2_7) + (3424565047039/1000000000000 : ℝ)*(sp_s2_8) + (856141316057/250000000000 : ℝ)*(sp_s2_9) + (481564582411/250000000000 : ℝ)*(sp_s2_13) + (42063709/500000000000 : ℝ)*(sp_s2_14) + (21719/100000000000 : ℝ)*(sp_s2_15) + (317284515731/200000000000 : ℝ)*(f.failure) + (856141316057/250000000000 : ℝ)*(f.sum) + (957985226844581777/3601567150000000000000000000000 : ℝ)*base62 + (157421277491/69710000000000000000000000 : ℝ)*base64 + (1921572482167859/7233100000000000000000000000 : ℝ)*base66 + (115394388270071/139420000000000000000000000 : ℝ)*base68 + (3105165018270571169/50395450300000000000000000000000 : ℝ)*base71 + (5662317710487729/7229300000000000000000000000 : ℝ)*base72 + (29836448338429/1033300000000000000000000000 : ℝ)*base74 + (1403209611551751/7229300000000000000000000000 : ℝ)*base76 + (61451992132226617263/261451249150000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (4597/5000000000000000 : ℝ)*base87 + (4597/5000000000000000 : ℝ)*base89 + (4597/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29233/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29233/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1242421937032016375456060344179/364515331564930000000000000000000000 : ℝ) := by norm_num
    linear_combination (24364230747/62500000000 : ℝ)*(base7) + (216203/1000000000000 : ℝ)*(base49) + (248135318957/100000000000 : ℝ)*(major_s2_0) + (248135318957/100000000000 : ℝ)*(major_s2_1) + (248135318957/100000000000 : ℝ)*(major_s2_2) + (49907/50000000000 : ℝ)*(sp_s2_1) + (390689/500000000000 : ℝ)*(sp_s2_2) + (9438521/500000000000 : ℝ)*(sp_s2_8) + (201214693753/62500000000 : ℝ)*(sp_s2_14) + (804854168897/250000000000 : ℝ)*(sp_s2_15) + (3219435769391/1000000000000 : ℝ)*(sp_s2_16) + (949816167393/500000000000 : ℝ)*(sp_s2_20) + (725361/500000000000 : ℝ)*(sp_s2_21) + (5918893/500000000000 : ℝ)*(sp_s2_27) + (75490824031/50000000000 : ℝ)*(f.failure) + (321943655077/100000000000 : ℝ)*(f.sum) + (1740291022550397/4501958937500000000000000000 : ℝ)*base63 + (936096703203/8713750000000000000000000 : ℝ)*base65 + (78169572179677/723310000000000000000000000 : ℝ)*base67 + (19914910456357/69710000000000000000000000 : ℝ)*base69 + (865188739027210601/5039545030000000000000000000000 : ℝ)*base71 + (63112430425791/722930000000000000000000000 : ℝ)*base73 + (9880335966127/10333000000000000000000000 : ℝ)*base75 + (433200626971061/722930000000000000000000000 : ℝ)*base77 + (447178940410099769/2614512491500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (803/1250000000000000 : ℝ)*base86 + (803/1250000000000000 : ℝ)*base88 + (803/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28023/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28023/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43920673340483340239169/3616550000000000000000000000 : ℝ) := by norm_num
    linear_combination (11951099203/31250000000 : ℝ)*(base7) + (159347503437/1000000000000 : ℝ)*(base40) + (757699/500000000000 : ℝ)*(base49) + (2360889908941/1000000000000 : ℝ)*(major_s2_0) + (2360889908941/1000000000000 : ℝ)*(major_s2_1) + (2360889908941/1000000000000 : ℝ)*(major_s2_2) + (643047/50000000000 : ℝ)*(sp_s2_1) + (27720751/1000000000000 : ℝ)*(sp_s2_2) + (17990959/200000000000 : ℝ)*(sp_s2_9) + (2732233/125000000000 : ℝ)*(sp_s2_20) + (3056231846321/1000000000000 : ℝ)*(sp_s2_21) + (3056218985381/1000000000000 : ℝ)*(sp_s2_22) + (122244566831/40000000000 : ℝ)*(sp_s2_23) + (1818932111471/1000000000000 : ℝ)*(sp_s2_27) + (718259397419/500000000000 : ℝ)*(f.failure) + (3056231846321/1000000000000 : ℝ)*(f.sum) + (319776742172785273/1800783575000000000000000000000 : ℝ)*base62 + (6187917653923/34855000000000000000000000 : ℝ)*base65 + (525183119646917/7233100000000000000000000000 : ℝ)*base66 + (353954303263/27884000000000000000000000 : ℝ)*base69 + (2558456523386528093/50395450300000000000000000000000 : ℝ)*base70 + (1505967604531993/7229300000000000000000000000 : ℝ)*base73 + (44148733799913/1033300000000000000000000000 : ℝ)*base75 + (1294564106108497/7229300000000000000000000000 : ℝ)*base77 + (280401988282437009/1021293941992187500000000000000 : ℝ)*base78 + (8047/12500000000000000 : ℝ)*base86 + (8047/12500000000000000 : ℝ)*base88 + (8047/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((72293/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72293/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(72331/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6971/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6971/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((28879/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28879/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29233/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29233/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28023/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28023/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311063_s2 p hpa hpb X hX hprev1

#print axioms solution

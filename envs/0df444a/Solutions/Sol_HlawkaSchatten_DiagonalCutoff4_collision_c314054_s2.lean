-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314054_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:53.438272+00:00
-- url     : https://prove2.me/submissions/0f63d73e-3bca-4531-a3d7-b9262354b8f7

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
theorem collision_support_c314054_s2_s2_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1269509167/10000000000 : ℝ)*x 0 + (565509653/1250000000 : ℝ)*x 1 + (-795076447/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1269509167/10000000000 : ℝ)^75 ≤ (7253607227397/100000000000000 : ℝ)^59 := by
    have hnat : (1269509167 : ℕ)^75*100000000000000^59 ≤ 7253607227397^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269509167 10000000000 7253607227397 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565509653/1250000000 : ℝ)^75 ≤ (18242502869251/50000000000000 : ℝ)^59 := by
    have hnat : (565509653 : ℕ)^75*50000000000000^59 ≤ 18242502869251^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565509653 1250000000 18242502869251 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795076447/1250000000 : ℝ)^75 ≤ (56261387020537/100000000000000 : ℝ)^59 := by
    have hnat : (795076447 : ℕ)^75*100000000000000^59 ≤ 56261387020537^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795076447 1250000000 56261387020537 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1269509167/10000000000 : ℝ), (565509653/1250000000 : ℝ), (-795076447/1250000000 : ℝ)] ![(7253607227397/100000000000000 : ℝ), (18242502869251/50000000000000 : ℝ), (56261387020537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1269509167/10000000000 : ℝ)|^75 ≤ (7253607227397/100000000000000 : ℝ)^59
        have hw : |(-1269509167/10000000000 : ℝ)|=(1269509167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565509653/1250000000 : ℝ)|^75 ≤ (18242502869251/50000000000000 : ℝ)^59
        have hw : |(565509653/1250000000 : ℝ)|=(565509653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-795076447/1250000000 : ℝ)|^75 ≤ (56261387020537/100000000000000 : ℝ)^59
        have hw : |(-795076447/1250000000 : ℝ)|=(795076447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1027989219/2000000000 : ℝ)*x 0 + (2556300369/5000000000 : ℝ)*x 1 + (87408603/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027989219/2000000000 : ℝ)^75 ≤ (21455787071799/50000000000000 : ℝ)^59 := by
    have hnat : (1027989219 : ℕ)^75*50000000000000^59 ≤ 21455787071799^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027989219 2000000000 21455787071799 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2556300369/5000000000 : ℝ)^75 ≤ (10655394049479/25000000000000 : ℝ)^59 := by
    have hnat : (2556300369 : ℕ)^75*25000000000000^59 ≤ 10655394049479^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556300369 5000000000 10655394049479 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87408603/400000000 : ℝ)^75 ≤ (14466849639211/100000000000000 : ℝ)^59 := by
    have hnat : (87408603 : ℕ)^75*100000000000000^59 ≤ 14466849639211^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87408603 400000000 14466849639211 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1027989219/2000000000 : ℝ), (2556300369/5000000000 : ℝ), (87408603/400000000 : ℝ)] ![(21455787071799/50000000000000 : ℝ), (10655394049479/25000000000000 : ℝ), (14466849639211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1027989219/2000000000 : ℝ)|^75 ≤ (21455787071799/50000000000000 : ℝ)^59
        have hw : |(1027989219/2000000000 : ℝ)|=(1027989219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2556300369/5000000000 : ℝ)|^75 ≤ (10655394049479/25000000000000 : ℝ)^59
        have hw : |(2556300369/5000000000 : ℝ)|=(2556300369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(87408603/400000000 : ℝ)|^75 ≤ (14466849639211/100000000000000 : ℝ)^59
        have hw : |(87408603/400000000 : ℝ)|=(87408603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1157825223/10000000000 : ℝ)*x 0 + (1040188343/2500000000 : ℝ)*x 1 + (-6756167207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1157825223/10000000000 : ℝ)^75 ≤ (3226158426261/50000000000000 : ℝ)^59 := by
    have hnat : (1157825223 : ℕ)^75*50000000000000^59 ≤ 3226158426261^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157825223 10000000000 3226158426261 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040188343/2500000000 : ℝ)^75 ≤ (6560343392673/20000000000000 : ℝ)^59 := by
    have hnat : (1040188343 : ℕ)^75*20000000000000^59 ≤ 6560343392673^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040188343 2500000000 6560343392673 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6756167207/10000000000 : ℝ)^75 ≤ (12149193236157/20000000000000 : ℝ)^59 := by
    have hnat : (6756167207 : ℕ)^75*20000000000000^59 ≤ 12149193236157^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6756167207 10000000000 12149193236157 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1157825223/10000000000 : ℝ), (1040188343/2500000000 : ℝ), (-6756167207/10000000000 : ℝ)] ![(3226158426261/50000000000000 : ℝ), (6560343392673/20000000000000 : ℝ), (12149193236157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1157825223/10000000000 : ℝ)|^75 ≤ (3226158426261/50000000000000 : ℝ)^59
        have hw : |(-1157825223/10000000000 : ℝ)|=(1157825223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040188343/2500000000 : ℝ)|^75 ≤ (6560343392673/20000000000000 : ℝ)^59
        have hw : |(1040188343/2500000000 : ℝ)|=(1040188343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6756167207/10000000000 : ℝ)|^75 ≤ (12149193236157/20000000000000 : ℝ)^59
        have hw : |(-6756167207/10000000000 : ℝ)|=(6756167207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1328628539/2500000000 : ℝ)*x 0 + (-1585332967/10000000000 : ℝ)*x 1 + (-1078447737/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328628539/2500000000 : ℝ)^75 ≤ (11193167919869/25000000000000 : ℝ)^59 := by
    have hnat : (1328628539 : ℕ)^75*25000000000000^59 ≤ 11193167919869^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328628539 2500000000 11193167919869 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1585332967/10000000000 : ℝ)^75 ≤ (300645034593/3125000000000 : ℝ)^59 := by
    have hnat : (1585332967 : ℕ)^75*3125000000000^59 ≤ 300645034593^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585332967 10000000000 300645034593 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078447737/2000000000 : ℝ)^75 ≤ (11401671799107/25000000000000 : ℝ)^59 := by
    have hnat : (1078447737 : ℕ)^75*25000000000000^59 ≤ 11401671799107^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078447737 2000000000 11401671799107 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328628539/2500000000 : ℝ), (-1585332967/10000000000 : ℝ), (-1078447737/2000000000 : ℝ)] ![(11193167919869/25000000000000 : ℝ), (300645034593/3125000000000 : ℝ), (11401671799107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328628539/2500000000 : ℝ)|^75 ≤ (11193167919869/25000000000000 : ℝ)^59
        have hw : |(1328628539/2500000000 : ℝ)|=(1328628539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1585332967/10000000000 : ℝ)|^75 ≤ (300645034593/3125000000000 : ℝ)^59
        have hw : |(-1585332967/10000000000 : ℝ)|=(1585332967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1078447737/2000000000 : ℝ)|^75 ≤ (11401671799107/25000000000000 : ℝ)^59
        have hw : |(-1078447737/2000000000 : ℝ)|=(1078447737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4867602531/10000000000 : ℝ)*x 0 + (296281201/500000000 : ℝ)*x 1 + (360911007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4867602531/10000000000 : ℝ)^75 ≤ (20021158774187/50000000000000 : ℝ)^59 := by
    have hnat : (4867602531 : ℕ)^75*50000000000000^59 ≤ 20021158774187^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867602531 10000000000 20021158774187 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296281201/500000000 : ℝ)^75 ≤ (25708258833227/50000000000000 : ℝ)^59 := by
    have hnat : (296281201 : ℕ)^75*50000000000000^59 ≤ 25708258833227^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296281201 500000000 25708258833227 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (360911007/2500000000 : ℝ)^75 ≤ (4270582384057/50000000000000 : ℝ)^59 := by
    have hnat : (360911007 : ℕ)^75*50000000000000^59 ≤ 4270582384057^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360911007 2500000000 4270582384057 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4867602531/10000000000 : ℝ), (296281201/500000000 : ℝ), (360911007/2500000000 : ℝ)] ![(20021158774187/50000000000000 : ℝ), (25708258833227/50000000000000 : ℝ), (4270582384057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4867602531/10000000000 : ℝ)|^75 ≤ (20021158774187/50000000000000 : ℝ)^59
        have hw : |(4867602531/10000000000 : ℝ)|=(4867602531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(296281201/500000000 : ℝ)|^75 ≤ (25708258833227/50000000000000 : ℝ)^59
        have hw : |(296281201/500000000 : ℝ)|=(296281201/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(360911007/2500000000 : ℝ)|^75 ≤ (4270582384057/50000000000000 : ℝ)^59
        have hw : |(360911007/2500000000 : ℝ)|=(360911007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5024352529/10000000000 : ℝ)*x 0 + (739840023/1250000000 : ℝ)*x 1 + (-1230441187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5024352529/10000000000 : ℝ)^75 ≤ (2084428896941/5000000000000 : ℝ)^59 := by
    have hnat : (5024352529 : ℕ)^75*5000000000000^59 ≤ 2084428896941^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024352529 10000000000 2084428896941 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (739840023/1250000000 : ℝ)^75 ≤ (51340379984247/100000000000000 : ℝ)^59 := by
    have hnat : (739840023 : ℕ)^75*100000000000000^59 ≤ 51340379984247^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739840023 1250000000 51340379984247 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1230441187/10000000000 : ℝ)^75 ≤ (6971042064991/100000000000000 : ℝ)^59 := by
    have hnat : (1230441187 : ℕ)^75*100000000000000^59 ≤ 6971042064991^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230441187 10000000000 6971042064991 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5024352529/10000000000 : ℝ), (739840023/1250000000 : ℝ), (-1230441187/10000000000 : ℝ)] ![(2084428896941/5000000000000 : ℝ), (51340379984247/100000000000000 : ℝ), (6971042064991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5024352529/10000000000 : ℝ)|^75 ≤ (2084428896941/5000000000000 : ℝ)^59
        have hw : |(5024352529/10000000000 : ℝ)|=(5024352529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(739840023/1250000000 : ℝ)|^75 ≤ (51340379984247/100000000000000 : ℝ)^59
        have hw : |(739840023/1250000000 : ℝ)|=(739840023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1230441187/10000000000 : ℝ)|^75 ≤ (6971042064991/100000000000000 : ℝ)^59
        have hw : |(-1230441187/10000000000 : ℝ)|=(1230441187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-90479099/1250000000 : ℝ)*x 0 + (1125980941/2500000000 : ℝ)*x 1 + (-1676434549/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90479099/1250000000 : ℝ)^75 ≤ (1775651021699/50000000000000 : ℝ)^59 := by
    have hnat : (90479099 : ℕ)^75*50000000000000^59 ≤ 1775651021699^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90479099 1250000000 1775651021699 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125980941/2500000000 : ℝ)^75 ≤ (7255704900749/20000000000000 : ℝ)^59 := by
    have hnat : (1125980941 : ℕ)^75*20000000000000^59 ≤ 7255704900749^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125980941 2500000000 7255704900749 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1676434549/2500000000 : ℝ)^75 ≤ (60170173433139/100000000000000 : ℝ)^59 := by
    have hnat : (1676434549 : ℕ)^75*100000000000000^59 ≤ 60170173433139^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676434549 2500000000 60170173433139 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-90479099/1250000000 : ℝ), (1125980941/2500000000 : ℝ), (-1676434549/2500000000 : ℝ)] ![(1775651021699/50000000000000 : ℝ), (7255704900749/20000000000000 : ℝ), (60170173433139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-90479099/1250000000 : ℝ)|^75 ≤ (1775651021699/50000000000000 : ℝ)^59
        have hw : |(-90479099/1250000000 : ℝ)|=(90479099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125980941/2500000000 : ℝ)|^75 ≤ (7255704900749/20000000000000 : ℝ)^59
        have hw : |(1125980941/2500000000 : ℝ)|=(1125980941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1676434549/2500000000 : ℝ)|^75 ≤ (60170173433139/100000000000000 : ℝ)^59
        have hw : |(-1676434549/2500000000 : ℝ)|=(1676434549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4988865121/10000000000 : ℝ)*x 0 + (-1988169519/10000000000 : ℝ)*x 1 + (-2707709161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4988865121/10000000000 : ℝ)^75 ≤ (1032865910957/2500000000000 : ℝ)^59 := by
    have hnat : (4988865121 : ℕ)^75*2500000000000^59 ≤ 1032865910957^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988865121 10000000000 1032865910957 2500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988169519/10000000000 : ℝ)^75 ≤ (6414657800317/50000000000000 : ℝ)^59 := by
    have hnat : (1988169519 : ℕ)^75*50000000000000^59 ≤ 6414657800317^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988169519 10000000000 6414657800317 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707709161/5000000000 : ℝ)^75 ≤ (5732005993863/12500000000000 : ℝ)^59 := by
    have hnat : (2707709161 : ℕ)^75*12500000000000^59 ≤ 5732005993863^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707709161 5000000000 5732005993863 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4988865121/10000000000 : ℝ), (-1988169519/10000000000 : ℝ), (-2707709161/5000000000 : ℝ)] ![(1032865910957/2500000000000 : ℝ), (6414657800317/50000000000000 : ℝ), (5732005993863/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4988865121/10000000000 : ℝ)|^75 ≤ (1032865910957/2500000000000 : ℝ)^59
        have hw : |(4988865121/10000000000 : ℝ)|=(4988865121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1988169519/10000000000 : ℝ)|^75 ≤ (6414657800317/50000000000000 : ℝ)^59
        have hw : |(-1988169519/10000000000 : ℝ)|=(1988169519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2707709161/5000000000 : ℝ)|^75 ≤ (5732005993863/12500000000000 : ℝ)^59
        have hw : |(-2707709161/5000000000 : ℝ)|=(2707709161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (238757183/400000000 : ℝ)*x 0 + (4838489779/10000000000 : ℝ)*x 1 + (177558101/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (238757183/400000000 : ℝ)^75 ≤ (12973663243173/25000000000000 : ℝ)^59 := by
    have hnat : (238757183 : ℕ)^75*25000000000000^59 ≤ 12973663243173^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238757183 400000000 12973663243173 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4838489779/10000000000 : ℝ)^75 ≤ (19869064187583/50000000000000 : ℝ)^59 := by
    have hnat : (4838489779 : ℕ)^75*50000000000000^59 ≤ 19869064187583^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838489779 10000000000 19869064187583 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177558101/1250000000 : ℝ)^75 ≤ (8367218626823/100000000000000 : ℝ)^59 := by
    have hnat : (177558101 : ℕ)^75*100000000000000^59 ≤ 8367218626823^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177558101 1250000000 8367218626823 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(238757183/400000000 : ℝ), (4838489779/10000000000 : ℝ), (177558101/1250000000 : ℝ)] ![(12973663243173/25000000000000 : ℝ), (19869064187583/50000000000000 : ℝ), (8367218626823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(238757183/400000000 : ℝ)|^75 ≤ (12973663243173/25000000000000 : ℝ)^59
        have hw : |(238757183/400000000 : ℝ)|=(238757183/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4838489779/10000000000 : ℝ)|^75 ≤ (19869064187583/50000000000000 : ℝ)^59
        have hw : |(4838489779/10000000000 : ℝ)|=(4838489779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(177558101/1250000000 : ℝ)|^75 ≤ (8367218626823/100000000000000 : ℝ)^59
        have hw : |(177558101/1250000000 : ℝ)|=(177558101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (736813537/1250000000 : ℝ)*x 0 + (4964373909/10000000000 : ℝ)*x 1 + (-676778749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (736813537/1250000000 : ℝ)^75 ≤ (25536777043363/50000000000000 : ℝ)^59 := by
    have hnat : (736813537 : ℕ)^75*50000000000000^59 ≤ 25536777043363^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736813537 1250000000 25536777043363 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4964373909/10000000000 : ℝ)^75 ≤ (20528492618463/50000000000000 : ℝ)^59 := by
    have hnat : (4964373909 : ℕ)^75*50000000000000^59 ≤ 20528492618463^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4964373909 10000000000 20528492618463 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676778749/5000000000 : ℝ)^75 ≤ (3074008073/39062500000 : ℝ)^59 := by
    have hnat : (676778749 : ℕ)^75*39062500000^59 ≤ 3074008073^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676778749 5000000000 3074008073 39062500000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(736813537/1250000000 : ℝ), (4964373909/10000000000 : ℝ), (-676778749/5000000000 : ℝ)] ![(25536777043363/50000000000000 : ℝ), (20528492618463/50000000000000 : ℝ), (3074008073/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(736813537/1250000000 : ℝ)|^75 ≤ (25536777043363/50000000000000 : ℝ)^59
        have hw : |(736813537/1250000000 : ℝ)|=(736813537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4964373909/10000000000 : ℝ)|^75 ≤ (20528492618463/50000000000000 : ℝ)^59
        have hw : |(4964373909/10000000000 : ℝ)|=(4964373909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-676778749/5000000000 : ℝ)|^75 ≤ (3074008073/39062500000 : ℝ)^59
        have hw : |(-676778749/5000000000 : ℝ)|=(676778749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-130324889/2500000000 : ℝ)*x 0 + (1026218229/2000000000 : ℝ)*x 1 + (-6234084983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130324889/2500000000 : ℝ)^75 ≤ (146237535189/6250000000000 : ℝ)^59 := by
    have hnat : (130324889 : ℕ)^75*6250000000000^59 ≤ 146237535189^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130324889 2500000000 146237535189 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026218229/2000000000 : ℝ)^75 ≤ (5352202667531/12500000000000 : ℝ)^59 := by
    have hnat : (1026218229 : ℕ)^75*12500000000000^59 ≤ 5352202667531^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026218229 2000000000 5352202667531 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6234084983/10000000000 : ℝ)^75 ≤ (27421289039427/50000000000000 : ℝ)^59 := by
    have hnat : (6234084983 : ℕ)^75*50000000000000^59 ≤ 27421289039427^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6234084983 10000000000 27421289039427 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130324889/2500000000 : ℝ), (1026218229/2000000000 : ℝ), (-6234084983/10000000000 : ℝ)] ![(146237535189/6250000000000 : ℝ), (5352202667531/12500000000000 : ℝ), (27421289039427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130324889/2500000000 : ℝ)|^75 ≤ (146237535189/6250000000000 : ℝ)^59
        have hw : |(-130324889/2500000000 : ℝ)|=(130324889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026218229/2000000000 : ℝ)|^75 ≤ (5352202667531/12500000000000 : ℝ)^59
        have hw : |(1026218229/2000000000 : ℝ)|=(1026218229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6234084983/10000000000 : ℝ)|^75 ≤ (27421289039427/50000000000000 : ℝ)^59
        have hw : |(-6234084983/10000000000 : ℝ)|=(6234084983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1575023093/2500000000 : ℝ)*x 0 + (-863508871/5000000000 : ℝ)*x 1 + (-4249297563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1575023093/2500000000 : ℝ)^75 ≤ (55581789071383/100000000000000 : ℝ)^59 := by
    have hnat : (1575023093 : ℕ)^75*100000000000000^59 ≤ 55581789071383^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1575023093 2500000000 55581789071383 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (863508871/5000000000 : ℝ)^75 ≤ (10726598690583/100000000000000 : ℝ)^59 := by
    have hnat : (863508871 : ℕ)^75*100000000000000^59 ≤ 10726598690583^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863508871 5000000000 10726598690583 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249297563/10000000000 : ℝ)^75 ≤ (4211451528103/12500000000000 : ℝ)^59 := by
    have hnat : (4249297563 : ℕ)^75*12500000000000^59 ≤ 4211451528103^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249297563 10000000000 4211451528103 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1575023093/2500000000 : ℝ), (-863508871/5000000000 : ℝ), (-4249297563/10000000000 : ℝ)] ![(55581789071383/100000000000000 : ℝ), (10726598690583/100000000000000 : ℝ), (4211451528103/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1575023093/2500000000 : ℝ)|^75 ≤ (55581789071383/100000000000000 : ℝ)^59
        have hw : |(1575023093/2500000000 : ℝ)|=(1575023093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-863508871/5000000000 : ℝ)|^75 ≤ (10726598690583/100000000000000 : ℝ)^59
        have hw : |(-863508871/5000000000 : ℝ)|=(863508871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4249297563/10000000000 : ℝ)|^75 ≤ (4211451528103/12500000000000 : ℝ)^59
        have hw : |(-4249297563/10000000000 : ℝ)|=(4249297563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (496147231/1000000000 : ℝ)*x 0 + (521706527/1000000000 : ℝ)*x 1 + (569197291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (496147231/1000000000 : ℝ)^75 ≤ (10256620695541/25000000000000 : ℝ)^59 := by
    have hnat : (496147231 : ℕ)^75*25000000000000^59 ≤ 10256620695541^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496147231 1000000000 10256620695541 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521706527/1000000000 : ℝ)^75 ≤ (8746334883703/20000000000000 : ℝ)^59 := by
    have hnat : (521706527 : ℕ)^75*20000000000000^59 ≤ 8746334883703^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521706527 1000000000 8746334883703 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569197291/2500000000 : ℝ)^75 ≤ (7620921392589/50000000000000 : ℝ)^59 := by
    have hnat : (569197291 : ℕ)^75*50000000000000^59 ≤ 7620921392589^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569197291 2500000000 7620921392589 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(496147231/1000000000 : ℝ), (521706527/1000000000 : ℝ), (569197291/2500000000 : ℝ)] ![(10256620695541/25000000000000 : ℝ), (8746334883703/20000000000000 : ℝ), (7620921392589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(496147231/1000000000 : ℝ)|^75 ≤ (10256620695541/25000000000000 : ℝ)^59
        have hw : |(496147231/1000000000 : ℝ)|=(496147231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521706527/1000000000 : ℝ)|^75 ≤ (8746334883703/20000000000000 : ℝ)^59
        have hw : |(521706527/1000000000 : ℝ)|=(521706527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(569197291/2500000000 : ℝ)|^75 ≤ (7620921392589/50000000000000 : ℝ)^59
        have hw : |(569197291/2500000000 : ℝ)|=(569197291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s2_s2_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (282367543/500000000 : ℝ)*x 0 + (493371171/1000000000 : ℝ)*x 1 + (-437178153/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (282367543/500000000 : ℝ)^75 ≤ (12091730129967/25000000000000 : ℝ)^59 := by
    have hnat : (282367543 : ℕ)^75*25000000000000^59 ≤ 12091730129967^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282367543 500000000 12091730129967 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493371171/1000000000 : ℝ)^75 ≤ (40734900083233/100000000000000 : ℝ)^59 := by
    have hnat : (493371171 : ℕ)^75*100000000000000^59 ≤ 40734900083233^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493371171 1000000000 40734900083233 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437178153/2500000000 : ℝ)^75 ≤ (10898179381581/100000000000000 : ℝ)^59 := by
    have hnat : (437178153 : ℕ)^75*100000000000000^59 ≤ 10898179381581^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437178153 2500000000 10898179381581 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(282367543/500000000 : ℝ), (493371171/1000000000 : ℝ), (-437178153/2500000000 : ℝ)] ![(12091730129967/25000000000000 : ℝ), (40734900083233/100000000000000 : ℝ), (10898179381581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(282367543/500000000 : ℝ)|^75 ≤ (12091730129967/25000000000000 : ℝ)^59
        have hw : |(282367543/500000000 : ℝ)|=(282367543/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(493371171/1000000000 : ℝ)|^75 ≤ (40734900083233/100000000000000 : ℝ)^59
        have hw : |(493371171/1000000000 : ℝ)|=(493371171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437178153/2500000000 : ℝ)|^75 ≤ (10898179381581/100000000000000 : ℝ)^59
        have hw : |(-437178153/2500000000 : ℝ)|=(437178153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314054_s2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((14183/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14183/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59683/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59683/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-48193/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-48193/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3139/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3139/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16507/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16507/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-531/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-531/2500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s2_pow0 : (14183/25000 : ℝ) ^ (37/8 : ℝ) ≤ (3634334862667513321/50000000000000000000 : ℝ) := by
    have hpowers : (14183/25000 : ℝ)^37 ≤ (3634334862667513321/50000000000000000000 : ℝ)^8 := by
      have hnat : (14183 : ℕ)^37*50000000000000000000^8 ≤ 3634334862667513321^8*25000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14183 25000 3634334862667513321 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14183/25000 : ℝ)) (X := (3634334862667513321/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (53634334862667513321/50000000000000000000 : ℝ) ≤ (2538216965912131/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (53634334862667513321/50000000000000000000 : ℝ)^8 ≤ (2538216965912131/2500000000000000 : ℝ)^37 := by
      have hnat : (53634334862667513321 : ℕ)^8*2500000000000000^37 ≤ 2538216965912131^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53634334862667513321 50000000000000000000 2538216965912131 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2538216965912131/2500000000000000 : ℝ)) (X := (53634334862667513321/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (28634334862667513321/25000000000000000000 : ℝ) ≤ (5148910244160747/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (28634334862667513321/25000000000000000000 : ℝ)^8 ≤ (5148910244160747/5000000000000000 : ℝ)^37 := by
      have hnat : (28634334862667513321 : ℕ)^8*5000000000000000^37 ≤ 5148910244160747^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28634334862667513321 25000000000000000000 5148910244160747 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5148910244160747/5000000000000000 : ℝ)) (X := (28634334862667513321/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(38216965912131/1418300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(14495262467297/567320000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (14183/25000 : ℝ)) (alpha := (38216965912131/1418300000000000 : ℝ)) (beta := (14495262467297/567320000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (14183/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(38216965912131/1418300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(14495262467297/567320000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (59683/100000 : ℝ) ^ (37/8 : ℝ) ≤ (1148733394416605017/12500000000000000000 : ℝ) := by
    have hpowers : (59683/100000 : ℝ)^37 ≤ (1148733394416605017/12500000000000000000 : ℝ)^8 := by
      have hnat : (59683 : ℕ)^37*12500000000000000000^8 ≤ 1148733394416605017^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59683 100000 1148733394416605017 12500000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59683/100000 : ℝ)) (X := (1148733394416605017/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (13648733394416605017/12500000000000000000 : ℝ) ≤ (5095955711169461/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (13648733394416605017/12500000000000000000 : ℝ)^8 ≤ (5095955711169461/5000000000000000 : ℝ)^37 := by
      have hnat : (13648733394416605017 : ℕ)^8*5000000000000000^37 ≤ 5095955711169461^37*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13648733394416605017 12500000000000000000 5095955711169461 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5095955711169461/5000000000000000 : ℝ)) (X := (13648733394416605017/12500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (7398733394416605017/6250000000000000000 : ℝ) ≤ (10371552109683619/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (7398733394416605017/6250000000000000000 : ℝ)^8 ≤ (10371552109683619/10000000000000000 : ℝ)^37 := by
      have hnat : (7398733394416605017 : ℕ)^8*10000000000000000^37 ≤ 10371552109683619^37*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7398733394416605017 6250000000000000000 10371552109683619 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10371552109683619/10000000000000000 : ℝ)) (X := (7398733394416605017/6250000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(7381208551497/229550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(179640687344697/5968300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (59683/100000 : ℝ)) (alpha := (7381208551497/229550000000000 : ℝ)) (beta := (179640687344697/5968300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (59683/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(7381208551497/229550000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(179640687344697/5968300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (48193/100000 : ℝ) ^ (37/8 : ℝ) ≤ (21363914975174903/625000000000000000 : ℝ) := by
    have hpowers : (48193/100000 : ℝ)^37 ≤ (21363914975174903/625000000000000000 : ℝ)^8 := by
      have hnat : (48193 : ℕ)^37*625000000000000000^8 ≤ 21363914975174903^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48193 100000 21363914975174903 625000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48193/100000 : ℝ)) (X := (21363914975174903/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (646363914975174903/625000000000000000 : ℝ) ≤ (402917488223013/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (646363914975174903/625000000000000000 : ℝ)^8 ≤ (402917488223013/400000000000000 : ℝ)^37 := by
      have hnat : (646363914975174903 : ℕ)^8*400000000000000^37 ≤ 402917488223013^37*625000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        646363914975174903 625000000000000000 402917488223013 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (402917488223013/400000000000000 : ℝ)) (X := (646363914975174903/625000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (333863914975174903/312500000000000000 : ℝ) ≤ (253600217484083/250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (333863914975174903/312500000000000000 : ℝ)^8 ≤ (253600217484083/250000000000000 : ℝ)^37 := by
      have hnat : (333863914975174903 : ℕ)^8*250000000000000^37 ≤ 253600217484083^37*312500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        333863914975174903 312500000000000000 253600217484083 250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (253600217484083/250000000000000 : ℝ)) (X := (333863914975174903/312500000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(2917488223013/192772000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(14214298757599/963860000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (48193/100000 : ℝ)) (alpha := (2917488223013/192772000000000 : ℝ)) (beta := (14214298757599/963860000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (48193/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(2917488223013/192772000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(14214298757599/963860000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1269509167/10000000000 : ℝ)*X 0 0+(565509653/1250000000 : ℝ)*X 0 1+(-795076447/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1027989219/2000000000 : ℝ)*X 2 0+(2556300369/5000000000 : ℝ)*X 2 1+(87408603/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1157825223/10000000000 : ℝ)*X 0 0+(1040188343/2500000000 : ℝ)*X 0 1+(-6756167207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1328628539/2500000000 : ℝ)*X 1 0+(-1585332967/10000000000 : ℝ)*X 1 1+(-1078447737/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4867602531/10000000000 : ℝ)*X 2 0+(296281201/500000000 : ℝ)*X 2 1+(360911007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((5024352529/10000000000 : ℝ)*X 0 0+(739840023/1250000000 : ℝ)*X 0 1+(-1230441187/10000000000 : ℝ)*X 0 2+(5024352529/10000000000 : ℝ)*X 1 0+(739840023/1250000000 : ℝ)*X 1 1+(-1230441187/10000000000 : ℝ)*X 1 2+(5024352529/10000000000 : ℝ)*X 2 0+(739840023/1250000000 : ℝ)*X 2 1+(-1230441187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-90479099/1250000000 : ℝ)*X 0 0+(1125980941/2500000000 : ℝ)*X 0 1+(-1676434549/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4988865121/10000000000 : ℝ)*X 1 0+(-1988169519/10000000000 : ℝ)*X 1 1+(-2707709161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((238757183/400000000 : ℝ)*X 2 0+(4838489779/10000000000 : ℝ)*X 2 1+(177558101/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((736813537/1250000000 : ℝ)*X 0 0+(4964373909/10000000000 : ℝ)*X 0 1+(-676778749/5000000000 : ℝ)*X 0 2+(736813537/1250000000 : ℝ)*X 1 0+(4964373909/10000000000 : ℝ)*X 1 1+(-676778749/5000000000 : ℝ)*X 1 2+(736813537/1250000000 : ℝ)*X 2 0+(4964373909/10000000000 : ℝ)*X 2 1+(-676778749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-130324889/2500000000 : ℝ)*X 0 0+(1026218229/2000000000 : ℝ)*X 0 1+(-6234084983/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1575023093/2500000000 : ℝ)*X 1 0+(-863508871/5000000000 : ℝ)*X 1 1+(-4249297563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((496147231/1000000000 : ℝ)*X 2 0+(521706527/1000000000 : ℝ)*X 2 1+(569197291/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((282367543/500000000 : ℝ)*X 0 0+(493371171/1000000000 : ℝ)*X 0 1+(-437178153/2500000000 : ℝ)*X 0 2+(282367543/500000000 : ℝ)*X 1 0+(493371171/1000000000 : ℝ)*X 1 1+(-437178153/2500000000 : ℝ)*X 1 2+(282367543/500000000 : ℝ)*X 2 0+(493371171/1000000000 : ℝ)*X 2 1+(-437178153/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((3139/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3139/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2524772600052564929134089/172854736718750000000000000000 : ℝ) := by norm_num
    linear_combination (109229056149/125000000000 : ℝ)*(base39) + (5595833/1000000000000 : ℝ)*(base50) + (101954241697/200000000000 : ℝ)*(base60) + (6338084059299/1000000000000 : ℝ)*(major_s2_0) + (6338084059299/1000000000000 : ℝ)*(major_s2_1) + (6338084059299/1000000000000 : ℝ)*(major_s2_2) + (11850217/250000000000 : ℝ)*(sp_s2_0) + (8992588563799/1000000000000 : ℝ)*(sp_s2_7) + (2248124724981/250000000000 : ℝ)*(sp_s2_8) + (8992607925813/1000000000000 : ℝ)*(sp_s2_9) + (3683454927557/1000000000000 : ℝ)*(sp_s2_13) + (72357589/1000000000000 : ℝ)*(sp_s2_14) + (52355583/250000000000 : ℝ)*(sp_s2_15) + (100396443/1000000000000 : ℝ)*(sp_s2_23) + (3683454927557/1000000000000 : ℝ)*(f.failure) + (562044270141/62500000000 : ℝ)*(f.sum) + (11820908265516851023/22125406300000000000000000000000 : ℝ)*base63 + (510539840507517/963860000000000000000000000 : ℝ)*base65 + (2499562025663283/5968300000000000000000000000 : ℝ)*base66 + (881809524899401/963860000000000000000000000 : ℝ)*base69 + (148797748375720853/4272008243750000000000000000000 : ℝ)*base70 + (397532584741001/567320000000000000000000000 : ℝ)*base72 + (218982970988473/229550000000000000000000000 : ℝ)*base75 + (1064624744091029/1418300000000000000000000000 : ℝ)*base77 + (2190859591620913099/13022830600000000000000000000000 : ℝ)*base79 + (94567/100000000000000000 : ℝ)*base86 + (94567/100000000000000000 : ℝ)*base88 + (94567/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16507/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16507/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28572489193958431861370557593/2413881827330000000000000000000000 : ℝ) := by norm_num
    linear_combination (202512855711/250000000000 : ℝ)*(base39) + (112108847803/500000000000 : ℝ)*(base60) + (1589286771201/250000000000 : ℝ)*(major_s2_0) + (1589286771201/250000000000 : ℝ)*(major_s2_1) + (1589286771201/250000000000 : ℝ)*(major_s2_2) + (64202901/250000000000 : ℝ)*(sp_s2_0) + (34811951/1000000000000 : ℝ)*(sp_s2_2) + (11205903/62500000000 : ℝ)*(sp_s2_8) + (2254849287117/250000000000 : ℝ)*(sp_s2_14) + (450978864601/50000000000 : ℝ)*(sp_s2_15) + (4509860887259/500000000000 : ℝ)*(sp_s2_16) + (3694117565933/1000000000000 : ℝ)*(sp_s2_20) + (102626397/1000000000000 : ℝ)*(sp_s2_21) + (208035811/500000000000 : ℝ)*(sp_s2_27) + (738906727511/200000000000 : ℝ)*(f.failure) + (9019756586469/1000000000000 : ℝ)*(f.sum) + (325147912008788723/5531351575000000000000000000000 : ℝ)*base62 + (54379992978823/120482500000000000000000000 : ℝ)*base64 + (1579386762470921/2984150000000000000000000000 : ℝ)*base67 + (2273753646649/240965000000000000000000000 : ℝ)*base68 + (6537315933078420059/34176065950000000000000000000000 : ℝ)*base70 + (37717176587791/141830000000000000000000000 : ℝ)*base73 + (116481698674677/229550000000000000000000000 : ℝ)*base74 + (361551947186793/709150000000000000000000000 : ℝ)*base76 + (477506917711379583/1627853825000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (10259/20000000000000000 : ℝ)*base87 + (10259/20000000000000000 : ℝ)*base89 + (10259/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-531/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-531/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1043661368810011750760169988929/156902318776450000000000000000000000 : ℝ) := by norm_num
    linear_combination (1472011/1000000000000 : ℝ)*(base11) + (1091859653029/1000000000000 : ℝ)*(base39) + (348701/500000000000 : ℝ)*(base40) + (820413/500000000000 : ℝ)*(base50) + (302006073667/62500000000 : ℝ)*(major_s2_0) + (302006073667/62500000000 : ℝ)*(major_s2_1) + (302006073667/62500000000 : ℝ)*(major_s2_2) + (88283/8000000000 : ℝ)*(sp_s2_2) + (22974223/1000000000000 : ℝ)*(sp_s2_9) + (55047231/500000000000 : ℝ)*(sp_s2_20) + (6855958401589/1000000000000 : ℝ)*(sp_s2_21) + (4284974921/625000000 : ℝ)*(sp_s2_22) + (3427962932001/500000000000 : ℝ)*(sp_s2_23) + (561624434411/200000000000 : ℝ)*(sp_s2_27) + (702058066629/250000000000 : ℝ)*(f.failure) + (4284974921/625000000 : ℝ)*(f.sum) + (421931240286573351/1382837893750000000000000000000 : ℝ)*base62 + (46558165708889/96386000000000000000000000 : ℝ)*base64 + (370721707867853/2984150000000000000000000000 : ℝ)*base67 + (52030956356699/120482500000000000000000000 : ℝ)*base68 + (1978084089186150139/4272008243750000000000000000000 : ℝ)*base70 + (4682936928879/35457500000000000000000000 : ℝ)*base72 + (44493110255533/114775000000000000000000000 : ℝ)*base74 + (191888945676777/354575000000000000000000000 : ℝ)*base76 + (549227136762925457/3255707650000000000000000000000 : ℝ)*base78 + (14599/25000000000000000 : ℝ)*base86 + (14599/25000000000000000 : ℝ)*base88 + (14599/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((14183/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14183/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59683/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59683/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-48193/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-48193/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3139/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3139/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16507/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16507/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-531/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-531/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314054_s2 p hpa hpb X hX hprev1

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:20:57.060419+00:00
-- url     : https://prove2.me/submissions/995b6085-ace3-4b98-83ab-51794e6b8fbd

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
theorem collision_support_c312063_s1_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-25713037/500000000 : ℝ)*x 0 + (5609583111/10000000000 : ℝ)*x 1 + (2913414531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25713037/500000000 : ℝ)^73 ≤ (2235683293093/100000000000000 : ℝ)^57 := by
    have hnat : (25713037 : ℕ)^73*100000000000000^57 ≤ 2235683293093^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25713037 500000000 2235683293093 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5609583111/10000000000 : ℝ)^73 ≤ (23846517609649/50000000000000 : ℝ)^57 := by
    have hnat : (5609583111 : ℕ)^73*50000000000000^57 ≤ 23846517609649^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5609583111 10000000000 23846517609649 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2913414531/5000000000 : ℝ)^73 ≤ (200285125911/400000000000 : ℝ)^57 := by
    have hnat : (2913414531 : ℕ)^73*400000000000^57 ≤ 200285125911^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2913414531 5000000000 200285125911 400000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25713037/500000000 : ℝ), (5609583111/10000000000 : ℝ), (2913414531/5000000000 : ℝ)] ![(2235683293093/100000000000000 : ℝ), (23846517609649/50000000000000 : ℝ), (200285125911/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25713037/500000000 : ℝ)|^73 ≤ (2235683293093/100000000000000 : ℝ)^57
        have hw : |(-25713037/500000000 : ℝ)|=(25713037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5609583111/10000000000 : ℝ)|^73 ≤ (23846517609649/50000000000000 : ℝ)^57
        have hw : |(5609583111/10000000000 : ℝ)|=(5609583111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2913414531/5000000000 : ℝ)|^73 ≤ (200285125911/400000000000 : ℝ)^57
        have hw : |(2913414531/5000000000 : ℝ)|=(2913414531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (350572801/625000000 : ℝ)*x 0 + (-502106129/10000000000 : ℝ)*x 1 + (5833370469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (350572801/625000000 : ℝ)^73 ≤ (11922120154127/25000000000000 : ℝ)^57 := by
    have hnat : (350572801 : ℕ)^73*25000000000000^57 ≤ 11922120154127^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350572801 625000000 11922120154127 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502106129/10000000000 : ℝ)^73 ≤ (135514748649/6250000000000 : ℝ)^57 := by
    have hnat : (502106129 : ℕ)^73*6250000000000^57 ≤ 135514748649^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502106129 10000000000 135514748649 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5833370469/10000000000 : ℝ)^73 ≤ (50143283386487/100000000000000 : ℝ)^57 := by
    have hnat : (5833370469 : ℕ)^73*100000000000000^57 ≤ 50143283386487^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5833370469 10000000000 50143283386487 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(350572801/625000000 : ℝ), (-502106129/10000000000 : ℝ), (5833370469/10000000000 : ℝ)] ![(11922120154127/25000000000000 : ℝ), (135514748649/6250000000000 : ℝ), (50143283386487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(350572801/625000000 : ℝ)|^73 ≤ (11922120154127/25000000000000 : ℝ)^57
        have hw : |(350572801/625000000 : ℝ)|=(350572801/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-502106129/10000000000 : ℝ)|^73 ≤ (135514748649/6250000000000 : ℝ)^57
        have hw : |(-502106129/10000000000 : ℝ)|=(502106129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5833370469/10000000000 : ℝ)|^73 ≤ (50143283386487/100000000000000 : ℝ)^57
        have hw : |(5833370469/10000000000 : ℝ)|=(5833370469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (707550121/1250000000 : ℝ)*x 0 + (290457069/500000000 : ℝ)*x 1 + (-448479361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (707550121/1250000000 : ℝ)^73 ≤ (12061768245967/25000000000000 : ℝ)^57 := by
    have hnat : (707550121 : ℕ)^73*25000000000000^57 ≤ 12061768245967^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707550121 1250000000 12061768245967 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290457069/500000000 : ℝ)^73 ≤ (12469176270741/25000000000000 : ℝ)^57 := by
    have hnat : (290457069 : ℕ)^73*25000000000000^57 ≤ 12469176270741^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290457069 500000000 12469176270741 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448479361/10000000000 : ℝ)^73 ≤ (1876221918707/100000000000000 : ℝ)^57 := by
    have hnat : (448479361 : ℕ)^73*100000000000000^57 ≤ 1876221918707^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448479361 10000000000 1876221918707 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(707550121/1250000000 : ℝ), (290457069/500000000 : ℝ), (-448479361/10000000000 : ℝ)] ![(12061768245967/25000000000000 : ℝ), (12469176270741/25000000000000 : ℝ), (1876221918707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(707550121/1250000000 : ℝ)|^73 ≤ (12061768245967/25000000000000 : ℝ)^57
        have hw : |(707550121/1250000000 : ℝ)|=(707550121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(290457069/500000000 : ℝ)|^73 ≤ (12469176270741/25000000000000 : ℝ)^57
        have hw : |(290457069/500000000 : ℝ)|=(290457069/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-448479361/10000000000 : ℝ)|^73 ≤ (1876221918707/100000000000000 : ℝ)^57
        have hw : |(-448479361/10000000000 : ℝ)|=(448479361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2306600639/5000000000 : ℝ)*x 0 + (4278715039/10000000000 : ℝ)*x 1 + (955024203/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2306600639/5000000000 : ℝ)^73 ≤ (37126780371417/100000000000000 : ℝ)^57 := by
    have hnat : (2306600639 : ℕ)^73*100000000000000^57 ≤ 37126780371417^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306600639 5000000000 37126780371417 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4278715039/10000000000 : ℝ)^73 ≤ (3371493897413/10000000000000 : ℝ)^57 := by
    have hnat : (4278715039 : ℕ)^73*10000000000000^57 ≤ 3371493897413^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278715039 10000000000 3371493897413 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955024203/2500000000 : ℝ)^73 ≤ (2915828063677/10000000000000 : ℝ)^57 := by
    have hnat : (955024203 : ℕ)^73*10000000000000^57 ≤ 2915828063677^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955024203 2500000000 2915828063677 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2306600639/5000000000 : ℝ), (4278715039/10000000000 : ℝ), (955024203/2500000000 : ℝ)] ![(37126780371417/100000000000000 : ℝ), (3371493897413/10000000000000 : ℝ), (2915828063677/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2306600639/5000000000 : ℝ)|^73 ≤ (37126780371417/100000000000000 : ℝ)^57
        have hw : |(2306600639/5000000000 : ℝ)|=(2306600639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4278715039/10000000000 : ℝ)|^73 ≤ (3371493897413/10000000000000 : ℝ)^57
        have hw : |(4278715039/10000000000 : ℝ)|=(4278715039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(955024203/2500000000 : ℝ)|^73 ≤ (2915828063677/10000000000000 : ℝ)^57
        have hw : |(955024203/2500000000 : ℝ)|=(955024203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-284598219/2500000000 : ℝ)*x 0 + (2605029307/10000000000 : ℝ)*x 1 + (4033777159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284598219/2500000000 : ℝ)^73 ≤ (1546435227429/25000000000000 : ℝ)^57 := by
    have hnat : (284598219 : ℕ)^73*25000000000000^57 ≤ 1546435227429^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284598219 2500000000 1546435227429 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2605029307/10000000000 : ℝ)^73 ≤ (2232236485323/12500000000000 : ℝ)^57 := by
    have hnat : (2605029307 : ℕ)^73*12500000000000^57 ≤ 2232236485323^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605029307 10000000000 2232236485323 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033777159/5000000000 : ℝ)^73 ≤ (37978183598549/50000000000000 : ℝ)^57 := by
    have hnat : (4033777159 : ℕ)^73*50000000000000^57 ≤ 37978183598549^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033777159 5000000000 37978183598549 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-284598219/2500000000 : ℝ), (2605029307/10000000000 : ℝ), (4033777159/5000000000 : ℝ)] ![(1546435227429/25000000000000 : ℝ), (2232236485323/12500000000000 : ℝ), (37978183598549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-284598219/2500000000 : ℝ)|^73 ≤ (1546435227429/25000000000000 : ℝ)^57
        have hw : |(-284598219/2500000000 : ℝ)|=(284598219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2605029307/10000000000 : ℝ)|^73 ≤ (2232236485323/12500000000000 : ℝ)^57
        have hw : |(2605029307/10000000000 : ℝ)|=(2605029307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033777159/5000000000 : ℝ)|^73 ≤ (37978183598549/50000000000000 : ℝ)^57
        have hw : |(4033777159/5000000000 : ℝ)|=(4033777159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3225826211/10000000000 : ℝ)*x 0 + (-9360721/625000000 : ℝ)*x 1 + (1009503019/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3225826211/10000000000 : ℝ)^73 ≤ (23480947829831/100000000000000 : ℝ)^57 := by
    have hnat : (3225826211 : ℕ)^73*100000000000000^57 ≤ 23480947829831^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3225826211 10000000000 23480947829831 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9360721/625000000 : ℝ)^73 ≤ (92108366083/20000000000000 : ℝ)^57 := by
    have hnat : (9360721 : ℕ)^73*20000000000000^57 ≤ 92108366083^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9360721 625000000 92108366083 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009503019/1250000000 : ℝ)^73 ≤ (76058510327237/100000000000000 : ℝ)^57 := by
    have hnat : (1009503019 : ℕ)^73*100000000000000^57 ≤ 76058510327237^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009503019 1250000000 76058510327237 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3225826211/10000000000 : ℝ), (-9360721/625000000 : ℝ), (1009503019/1250000000 : ℝ)] ![(23480947829831/100000000000000 : ℝ), (92108366083/20000000000000 : ℝ), (76058510327237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3225826211/10000000000 : ℝ)|^73 ≤ (23480947829831/100000000000000 : ℝ)^57
        have hw : |(3225826211/10000000000 : ℝ)|=(3225826211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9360721/625000000 : ℝ)|^73 ≤ (92108366083/20000000000000 : ℝ)^57
        have hw : |(-9360721/625000000 : ℝ)|=(9360721/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1009503019/1250000000 : ℝ)|^73 ≤ (76058510327237/100000000000000 : ℝ)^57
        have hw : |(1009503019/1250000000 : ℝ)|=(1009503019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (395464653/1250000000 : ℝ)*x 0 + (4075338801/5000000000 : ℝ)*x 1 + (-1158167/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395464653/1250000000 : ℝ)^73 ≤ (458070433259/2000000000000 : ℝ)^57 := by
    have hnat : (395464653 : ℕ)^73*2000000000000^57 ≤ 458070433259^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395464653 1250000000 458070433259 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4075338801/5000000000 : ℝ)^73 ≤ (38480051040763/50000000000000 : ℝ)^57 := by
    have hnat : (4075338801 : ℕ)^73*50000000000000^57 ≤ 38480051040763^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4075338801 5000000000 38480051040763 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158167/200000000 : ℝ)^73 ≤ (34094060423/25000000000000 : ℝ)^57 := by
    have hnat : (1158167 : ℕ)^73*25000000000000^57 ≤ 34094060423^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158167 200000000 34094060423 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(395464653/1250000000 : ℝ), (4075338801/5000000000 : ℝ), (-1158167/200000000 : ℝ)] ![(458070433259/2000000000000 : ℝ), (38480051040763/50000000000000 : ℝ), (34094060423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(395464653/1250000000 : ℝ)|^73 ≤ (458070433259/2000000000000 : ℝ)^57
        have hw : |(395464653/1250000000 : ℝ)|=(395464653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4075338801/5000000000 : ℝ)|^73 ≤ (38480051040763/50000000000000 : ℝ)^57
        have hw : |(4075338801/5000000000 : ℝ)|=(4075338801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1158167/200000000 : ℝ)|^73 ≤ (34094060423/25000000000000 : ℝ)^57
        have hw : |(-1158167/200000000 : ℝ)|=(1158167/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (407693847/1250000000 : ℝ)*x 0 + (3638266579/5000000000 : ℝ)*x 1 + (25136653/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407693847/1250000000 : ℝ)^73 ≤ (23814498900783/100000000000000 : ℝ)^57 := by
    have hnat : (407693847 : ℕ)^73*100000000000000^57 ≤ 23814498900783^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407693847 1250000000 23814498900783 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3638266579/5000000000 : ℝ)^73 ≤ (33276411447447/50000000000000 : ℝ)^57 := by
    have hnat : (3638266579 : ℕ)^73*50000000000000^57 ≤ 33276411447447^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3638266579 5000000000 33276411447447 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25136653/156250000 : ℝ)^73 ≤ (481633909663/5000000000000 : ℝ)^57 := by
    have hnat : (25136653 : ℕ)^73*5000000000000^57 ≤ 481633909663^57*156250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25136653 156250000 481633909663 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(407693847/1250000000 : ℝ), (3638266579/5000000000 : ℝ), (25136653/156250000 : ℝ)] ![(23814498900783/100000000000000 : ℝ), (33276411447447/50000000000000 : ℝ), (481633909663/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(407693847/1250000000 : ℝ)|^73 ≤ (23814498900783/100000000000000 : ℝ)^57
        have hw : |(407693847/1250000000 : ℝ)|=(407693847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3638266579/5000000000 : ℝ)|^73 ≤ (33276411447447/50000000000000 : ℝ)^57
        have hw : |(3638266579/5000000000 : ℝ)|=(3638266579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25136653/156250000 : ℝ)|^73 ≤ (481633909663/5000000000000 : ℝ)^57
        have hw : |(25136653/156250000 : ℝ)|=(25136653/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13272013/1000000000 : ℝ)*x 0 + (788690121/2500000000 : ℝ)*x 1 + (4068096653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13272013/1000000000 : ℝ)^73 ≤ (394495328359/100000000000000 : ℝ)^57 := by
    have hnat : (13272013 : ℕ)^73*100000000000000^57 ≤ 394495328359^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13272013 1000000000 394495328359 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (788690121/2500000000 : ℝ)^73 ≤ (22820511768481/100000000000000 : ℝ)^57 := by
    have hnat : (788690121 : ℕ)^73*100000000000000^57 ≤ 22820511768481^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788690121 2500000000 22820511768481 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4068096653/5000000000 : ℝ)^73 ≤ (19196248223037/25000000000000 : ℝ)^57 := by
    have hnat : (4068096653 : ℕ)^73*25000000000000^57 ≤ 19196248223037^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4068096653 5000000000 19196248223037 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13272013/1000000000 : ℝ), (788690121/2500000000 : ℝ), (4068096653/5000000000 : ℝ)] ![(394495328359/100000000000000 : ℝ), (22820511768481/100000000000000 : ℝ), (19196248223037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13272013/1000000000 : ℝ)|^73 ≤ (394495328359/100000000000000 : ℝ)^57
        have hw : |(-13272013/1000000000 : ℝ)|=(13272013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(788690121/2500000000 : ℝ)|^73 ≤ (22820511768481/100000000000000 : ℝ)^57
        have hw : |(788690121/2500000000 : ℝ)|=(788690121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4068096653/5000000000 : ℝ)|^73 ≤ (19196248223037/25000000000000 : ℝ)^57
        have hw : |(4068096653/5000000000 : ℝ)|=(4068096653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2507885271/10000000000 : ℝ)*x 0 + (-1126339509/10000000000 : ℝ)*x 1 + (8144754631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2507885271/10000000000 : ℝ)^73 ≤ (17009528391657/100000000000000 : ℝ)^57 := by
    have hnat : (2507885271 : ℕ)^73*100000000000000^57 ≤ 17009528391657^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507885271 10000000000 17009528391657 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126339509/10000000000 : ℝ)^73 ≤ (1220397271067/20000000000000 : ℝ)^57 := by
    have hnat : (1126339509 : ℕ)^73*20000000000000^57 ≤ 1220397271067^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126339509 10000000000 1220397271067 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8144754631/10000000000 : ℝ)^73 ≤ (76888485229607/100000000000000 : ℝ)^57 := by
    have hnat : (8144754631 : ℕ)^73*100000000000000^57 ≤ 76888485229607^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8144754631 10000000000 76888485229607 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2507885271/10000000000 : ℝ), (-1126339509/10000000000 : ℝ), (8144754631/10000000000 : ℝ)] ![(17009528391657/100000000000000 : ℝ), (1220397271067/20000000000000 : ℝ), (76888485229607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2507885271/10000000000 : ℝ)|^73 ≤ (17009528391657/100000000000000 : ℝ)^57
        have hw : |(2507885271/10000000000 : ℝ)|=(2507885271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126339509/10000000000 : ℝ)|^73 ≤ (1220397271067/20000000000000 : ℝ)^57
        have hw : |(-1126339509/10000000000 : ℝ)|=(1126339509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8144754631/10000000000 : ℝ)|^73 ≤ (76888485229607/100000000000000 : ℝ)^57
        have hw : |(8144754631/10000000000 : ℝ)|=(8144754631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1589864817/2000000000 : ℝ)*x 0 + (3415964317/10000000000 : ℝ)*x 1 + (-77588341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1589864817/2000000000 : ℝ)^73 ≤ (9316713254613/12500000000000 : ℝ)^57 := by
    have hnat : (1589864817 : ℕ)^73*12500000000000^57 ≤ 9316713254613^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589864817 2000000000 9316713254613 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3415964317/10000000000 : ℝ)^73 ≤ (25267931883669/100000000000000 : ℝ)^57 := by
    have hnat : (3415964317 : ℕ)^73*100000000000000^57 ≤ 25267931883669^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3415964317 10000000000 25267931883669 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77588341/10000000000 : ℝ)^73 ≤ (99181034999/50000000000000 : ℝ)^57 := by
    have hnat : (77588341 : ℕ)^73*50000000000000^57 ≤ 99181034999^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77588341 10000000000 99181034999 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1589864817/2000000000 : ℝ), (3415964317/10000000000 : ℝ), (-77588341/10000000000 : ℝ)] ![(9316713254613/12500000000000 : ℝ), (25267931883669/100000000000000 : ℝ), (99181034999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1589864817/2000000000 : ℝ)|^73 ≤ (9316713254613/12500000000000 : ℝ)^57
        have hw : |(1589864817/2000000000 : ℝ)|=(1589864817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3415964317/10000000000 : ℝ)|^73 ≤ (25267931883669/100000000000000 : ℝ)^57
        have hw : |(3415964317/10000000000 : ℝ)|=(3415964317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77588341/10000000000 : ℝ)|^73 ≤ (99181034999/50000000000000 : ℝ)^57
        have hw : |(-77588341/10000000000 : ℝ)|=(77588341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (151782827/200000000 : ℝ)*x 0 + (2869646587/10000000000 : ℝ)*x 1 + (12783771/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151782827/200000000 : ℝ)^73 ≤ (2809457698899/4000000000000 : ℝ)^57 := by
    have hnat : (151782827 : ℕ)^73*4000000000000^57 ≤ 2809457698899^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151782827 200000000 2809457698899 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2869646587/10000000000 : ℝ)^73 ≤ (20213424605633/100000000000000 : ℝ)^57 := by
    have hnat : (2869646587 : ℕ)^73*100000000000000^57 ≤ 20213424605633^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2869646587 10000000000 20213424605633 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12783771/80000000 : ℝ)^73 ≤ (298441653027/3125000000000 : ℝ)^57 := by
    have hnat : (12783771 : ℕ)^73*3125000000000^57 ≤ 298441653027^57*80000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12783771 80000000 298441653027 3125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(151782827/200000000 : ℝ), (2869646587/10000000000 : ℝ), (12783771/80000000 : ℝ)] ![(2809457698899/4000000000000 : ℝ), (20213424605633/100000000000000 : ℝ), (298441653027/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(151782827/200000000 : ℝ)|^73 ≤ (2809457698899/4000000000000 : ℝ)^57
        have hw : |(151782827/200000000 : ℝ)|=(151782827/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2869646587/10000000000 : ℝ)|^73 ≤ (20213424605633/100000000000000 : ℝ)^57
        have hw : |(2869646587/10000000000 : ℝ)|=(2869646587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12783771/80000000 : ℝ)|^73 ≤ (298441653027/3125000000000 : ℝ)^57
        have hw : |(12783771/80000000 : ℝ)|=(12783771/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-83340771/5000000000 : ℝ)*x 0 + (7282293191/10000000000 : ℝ)*x 1 + (1048228791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83340771/5000000000 : ℝ)^73 ≤ (528163292063/100000000000000 : ℝ)^57 := by
    have hnat : (83340771 : ℕ)^73*100000000000000^57 ≤ 528163292063^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83340771 5000000000 528163292063 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7282293191/10000000000 : ℝ)^73 ≤ (66620301047317/100000000000000 : ℝ)^57 := by
    have hnat : (7282293191 : ℕ)^73*100000000000000^57 ≤ 66620301047317^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7282293191 10000000000 66620301047317 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048228791/2500000000 : ℝ)^73 ≤ (8212883910557/25000000000000 : ℝ)^57 := by
    have hnat : (1048228791 : ℕ)^73*25000000000000^57 ≤ 8212883910557^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048228791 2500000000 8212883910557 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83340771/5000000000 : ℝ), (7282293191/10000000000 : ℝ), (1048228791/2500000000 : ℝ)] ![(528163292063/100000000000000 : ℝ), (66620301047317/100000000000000 : ℝ), (8212883910557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83340771/5000000000 : ℝ)|^73 ≤ (528163292063/100000000000000 : ℝ)^57
        have hw : |(-83340771/5000000000 : ℝ)|=(83340771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7282293191/10000000000 : ℝ)|^73 ≤ (66620301047317/100000000000000 : ℝ)^57
        have hw : |(7282293191/10000000000 : ℝ)|=(7282293191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048228791/2500000000 : ℝ)|^73 ≤ (8212883910557/25000000000000 : ℝ)^57
        have hw : |(1048228791/2500000000 : ℝ)|=(1048228791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7915982791/10000000000 : ℝ)*x 0 + (-25167321/5000000000 : ℝ)*x 1 + (866750837/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7915982791/10000000000 : ℝ)^73 ≤ (18533394960929/25000000000000 : ℝ)^57 := by
    have hnat : (7915982791 : ℕ)^73*25000000000000^57 ≤ 18533394960929^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7915982791 10000000000 18533394960929 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25167321/5000000000 : ℝ)^73 ≤ (227932897/200000000000 : ℝ)^57 := by
    have hnat : (25167321 : ℕ)^73*200000000000^57 ≤ 227932897^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25167321 5000000000 227932897 200000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (866750837/2500000000 : ℝ)^73 ≤ (25752453699393/100000000000000 : ℝ)^57 := by
    have hnat : (866750837 : ℕ)^73*100000000000000^57 ≤ 25752453699393^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866750837 2500000000 25752453699393 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7915982791/10000000000 : ℝ), (-25167321/5000000000 : ℝ), (866750837/2500000000 : ℝ)] ![(18533394960929/25000000000000 : ℝ), (227932897/200000000000 : ℝ), (25752453699393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7915982791/10000000000 : ℝ)|^73 ≤ (18533394960929/25000000000000 : ℝ)^57
        have hw : |(7915982791/10000000000 : ℝ)|=(7915982791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25167321/5000000000 : ℝ)|^73 ≤ (227932897/200000000000 : ℝ)^57
        have hw : |(-25167321/5000000000 : ℝ)|=(25167321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(866750837/2500000000 : ℝ)|^73 ≤ (25752453699393/100000000000000 : ℝ)^57
        have hw : |(866750837/2500000000 : ℝ)|=(866750837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2356445721/10000000000 : ℝ)*x 0 + (4140124937/5000000000 : ℝ)*x 1 + (-1077345147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2356445721/10000000000 : ℝ)^73 ≤ (7852700016609/50000000000000 : ℝ)^57 := by
    have hnat : (2356445721 : ℕ)^73*50000000000000^57 ≤ 7852700016609^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356445721 10000000000 7852700016609 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4140124937/5000000000 : ℝ)^73 ≤ (78530451310277/100000000000000 : ℝ)^57 := by
    have hnat : (4140124937 : ℕ)^73*100000000000000^57 ≤ 78530451310277^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140124937 5000000000 78530451310277 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077345147/10000000000 : ℝ)^73 ≤ (2882074318271/50000000000000 : ℝ)^57 := by
    have hnat : (1077345147 : ℕ)^73*50000000000000^57 ≤ 2882074318271^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077345147 10000000000 2882074318271 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2356445721/10000000000 : ℝ), (4140124937/5000000000 : ℝ), (-1077345147/10000000000 : ℝ)] ![(7852700016609/50000000000000 : ℝ), (78530451310277/100000000000000 : ℝ), (2882074318271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2356445721/10000000000 : ℝ)|^73 ≤ (7852700016609/50000000000000 : ℝ)^57
        have hw : |(2356445721/10000000000 : ℝ)|=(2356445721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4140124937/5000000000 : ℝ)|^73 ≤ (78530451310277/100000000000000 : ℝ)^57
        have hw : |(4140124937/5000000000 : ℝ)|=(4140124937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1077345147/10000000000 : ℝ)|^73 ≤ (2882074318271/50000000000000 : ℝ)^57
        have hw : |(-1077345147/10000000000 : ℝ)|=(1077345147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s1_s1_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7723531211/10000000000 : ℝ)*x 0 + (2472009997/10000000000 : ℝ)*x 1 + (368691533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7723531211/10000000000 : ℝ)^73 ≤ (35916634749993/50000000000000 : ℝ)^57 := by
    have hnat : (7723531211 : ℕ)^73*50000000000000^57 ≤ 35916634749993^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7723531211 10000000000 35916634749993 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2472009997/10000000000 : ℝ)^73 ≤ (3339706878899/20000000000000 : ℝ)^57 := by
    have hnat : (2472009997 : ℕ)^73*20000000000000^57 ≤ 3339706878899^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472009997 10000000000 3339706878899 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368691533/2000000000 : ℝ)^73 ≤ (11468196099353/100000000000000 : ℝ)^57 := by
    have hnat : (368691533 : ℕ)^73*100000000000000^57 ≤ 11468196099353^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368691533 2000000000 11468196099353 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7723531211/10000000000 : ℝ), (2472009997/10000000000 : ℝ), (368691533/2000000000 : ℝ)] ![(35916634749993/50000000000000 : ℝ), (3339706878899/20000000000000 : ℝ), (11468196099353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7723531211/10000000000 : ℝ)|^73 ≤ (35916634749993/50000000000000 : ℝ)^57
        have hw : |(7723531211/10000000000 : ℝ)|=(7723531211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2472009997/10000000000 : ℝ)|^73 ≤ (3339706878899/20000000000000 : ℝ)^57
        have hw : |(2472009997/10000000000 : ℝ)|=(2472009997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(368691533/2000000000 : ℝ)|^73 ≤ (11468196099353/100000000000000 : ℝ)^57
        have hw : |(368691533/2000000000 : ℝ)|=(368691533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312063_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((16929/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16929/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8417/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8417/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10257/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10257/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((34549/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34549/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6919/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6919/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16649/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16649/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (178281/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (16929/20000 : ℝ) ^ (9/2 : ℝ) ≤ (23614344587407057483/50000000000000000000 : ℝ) := by
    have hpowers : (16929/20000 : ℝ)^9 ≤ (23614344587407057483/50000000000000000000 : ℝ)^2 := by
      have hnat : (16929 : ℕ)^9*50000000000000000000^2 ≤ 23614344587407057483^2*20000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16929 20000 23614344587407057483 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16929/20000 : ℝ)) (X := (23614344587407057483/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (73614344587407057483/50000000000000000000 : ℝ) ≤ (2724404965860907/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (73614344587407057483/50000000000000000000 : ℝ)^2 ≤ (2724404965860907/2500000000000000 : ℝ)^9 := by
      have hnat : (73614344587407057483 : ℕ)^2*2500000000000000^9 ≤ 2724404965860907^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73614344587407057483 50000000000000000000 2724404965860907 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2724404965860907/2500000000000000 : ℝ)) (X := (73614344587407057483/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (48614344587407057483/25000000000000000000 : ℝ) ≤ (579633143054939/500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (48614344587407057483/25000000000000000000 : ℝ)^2 ≤ (579633143054939/500000000000000 : ℝ)^9 := by
      have hnat : (48614344587407057483 : ℕ)^2*500000000000000^9 ≤ 579633143054939^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48614344587407057483 25000000000000000000 579633143054939 500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (579633143054939/500000000000000 : ℝ)) (X := (48614344587407057483/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(74801655286969/705375000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(14480062451149/176343750000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (16929/20000 : ℝ)) (alpha := (74801655286969/705375000000000 : ℝ)) (beta := (14480062451149/176343750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16929/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(74801655286969/705375000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(14480062451149/176343750000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8417/10000 : ℝ) ^ (9/2 : ℝ) ≤ (46047703122244037787/100000000000000000000 : ℝ) := by
    have hpowers : (8417/10000 : ℝ)^9 ≤ (46047703122244037787/100000000000000000000 : ℝ)^2 := by
      have hnat : (8417 : ℕ)^9*100000000000000000000^2 ≤ 46047703122244037787^2*10000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8417 10000 46047703122244037787 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8417/10000 : ℝ)) (X := (46047703122244037787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (146047703122244037787/100000000000000000000 : ℝ) ≤ (10878133510231539/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (146047703122244037787/100000000000000000000 : ℝ)^2 ≤ (10878133510231539/10000000000000000 : ℝ)^9 := by
      have hnat : (146047703122244037787 : ℕ)^2*10000000000000000^9 ≤ 10878133510231539^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        146047703122244037787 100000000000000000000 10878133510231539 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10878133510231539/10000000000000000 : ℝ)) (X := (146047703122244037787/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (96047703122244037787/50000000000000000000 : ℝ) ≤ (92489782928899/80000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (96047703122244037787/50000000000000000000 : ℝ)^2 ≤ (92489782928899/80000000000000 : ℝ)^9 := by
      have hnat : (96047703122244037787 : ℕ)^2*80000000000000^9 ≤ 92489782928899^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        96047703122244037787 50000000000000000000 92489782928899 80000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (92489782928899/80000000000000 : ℝ)) (X := (96047703122244037787/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(46217553170081/443000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(170772338970209/2104250000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (8417/10000 : ℝ)) (alpha := (46217553170081/443000000000000 : ℝ)) (beta := (170772338970209/2104250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8417/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(46217553170081/443000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(170772338970209/2104250000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (10257/12500 : ℝ) ^ (9/2 : ℝ) ≤ (20533668463339934847/50000000000000000000 : ℝ) := by
    have hpowers : (10257/12500 : ℝ)^9 ≤ (20533668463339934847/50000000000000000000 : ℝ)^2 := by
      have hnat : (10257 : ℕ)^9*50000000000000000000^2 ≤ 20533668463339934847^2*12500^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10257 12500 20533668463339934847 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10257/12500 : ℝ)) (X := (20533668463339934847/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (70533668463339934847/50000000000000000000 : ℝ) ≤ (10794583291944419/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (70533668463339934847/50000000000000000000 : ℝ)^2 ≤ (10794583291944419/10000000000000000 : ℝ)^9 := by
      have hnat : (70533668463339934847 : ℕ)^2*10000000000000000^9 ≤ 10794583291944419^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70533668463339934847 50000000000000000000 10794583291944419 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10794583291944419/10000000000000000 : ℝ)) (X := (70533668463339934847/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (45533668463339934847/25000000000000000000 : ℝ) ≤ (2856308012066249/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (45533668463339934847/25000000000000000000 : ℝ)^2 ≤ (2856308012066249/2500000000000000 : ℝ)^9 := by
      have hnat : (45533668463339934847 : ℕ)^2*2500000000000000^9 ≤ 2856308012066249^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45533668463339934847 25000000000000000000 2856308012066249 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2856308012066249/2500000000000000 : ℝ)) (X := (45533668463339934847/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(794583291944419/8205600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(210216252106859/2735200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (10257/12500 : ℝ)) (alpha := (794583291944419/8205600000000000 : ℝ)) (beta := (210216252106859/2735200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (10257/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(794583291944419/8205600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(210216252106859/2735200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-25713037/500000000 : ℝ)*X 0 0+(5609583111/10000000000 : ℝ)*X 0 1+(2913414531/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((350572801/625000000 : ℝ)*X 1 0+(-502106129/10000000000 : ℝ)*X 1 1+(5833370469/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((707550121/1250000000 : ℝ)*X 2 0+(290457069/500000000 : ℝ)*X 2 1+(-448479361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2306600639/5000000000 : ℝ)*X 0 0+(4278715039/10000000000 : ℝ)*X 0 1+(955024203/2500000000 : ℝ)*X 0 2+(2306600639/5000000000 : ℝ)*X 1 0+(4278715039/10000000000 : ℝ)*X 1 1+(955024203/2500000000 : ℝ)*X 1 2+(2306600639/5000000000 : ℝ)*X 2 0+(4278715039/10000000000 : ℝ)*X 2 1+(955024203/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-284598219/2500000000 : ℝ)*X 0 0+(2605029307/10000000000 : ℝ)*X 0 1+(4033777159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3225826211/10000000000 : ℝ)*X 1 0+(-9360721/625000000 : ℝ)*X 1 1+(1009503019/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((395464653/1250000000 : ℝ)*X 2 0+(4075338801/5000000000 : ℝ)*X 2 1+(-1158167/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((407693847/1250000000 : ℝ)*X 0 0+(3638266579/5000000000 : ℝ)*X 0 1+(25136653/156250000 : ℝ)*X 0 2+(407693847/1250000000 : ℝ)*X 1 0+(3638266579/5000000000 : ℝ)*X 1 1+(25136653/156250000 : ℝ)*X 1 2+(407693847/1250000000 : ℝ)*X 2 0+(3638266579/5000000000 : ℝ)*X 2 1+(25136653/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-13272013/1000000000 : ℝ)*X 0 0+(788690121/2500000000 : ℝ)*X 0 1+(4068096653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2507885271/10000000000 : ℝ)*X 1 0+(-1126339509/10000000000 : ℝ)*X 1 1+(8144754631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1589864817/2000000000 : ℝ)*X 2 0+(3415964317/10000000000 : ℝ)*X 2 1+(-77588341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((151782827/200000000 : ℝ)*X 0 0+(2869646587/10000000000 : ℝ)*X 0 1+(12783771/80000000 : ℝ)*X 0 2+(151782827/200000000 : ℝ)*X 1 0+(2869646587/10000000000 : ℝ)*X 1 1+(12783771/80000000 : ℝ)*X 1 2+(151782827/200000000 : ℝ)*X 2 0+(2869646587/10000000000 : ℝ)*X 2 1+(12783771/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-83340771/5000000000 : ℝ)*X 0 0+(7282293191/10000000000 : ℝ)*X 0 1+(1048228791/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7915982791/10000000000 : ℝ)*X 1 0+(-25167321/5000000000 : ℝ)*X 1 1+(866750837/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2356445721/10000000000 : ℝ)*X 2 0+(4140124937/5000000000 : ℝ)*X 2 1+(-1077345147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7723531211/10000000000 : ℝ)*X 0 0+(2472009997/10000000000 : ℝ)*X 0 1+(368691533/2000000000 : ℝ)*X 0 2+(7723531211/10000000000 : ℝ)*X 1 0+(2472009997/10000000000 : ℝ)*X 1 1+(368691533/2000000000 : ℝ)*X 1 2+(7723531211/10000000000 : ℝ)*X 2 0+(2472009997/10000000000 : ℝ)*X 2 1+(368691533/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((34549/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34549/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (102115156669795548858506159/7122486442500000000000000000000 : ℝ) := by norm_num
    linear_combination (12237713533/15625000000 : ℝ)*(base7) + (1678949/1000000000000 : ℝ)*(base50) + (6225325049/250000000000 : ℝ)*(base60) + (13727860093/8000000000 : ℝ)*(major_s1_0) + (13727860093/8000000000 : ℝ)*(major_s1_1) + (13727860093/8000000000 : ℝ)*(major_s1_2) + (4737167/500000000000 : ℝ)*(sp_s1_0) + (465481/500000000000 : ℝ)*(sp_s1_6) + (1938375299423/1000000000000 : ℝ)*(sp_s1_7) + (387689967879/200000000000 : ℝ)*(sp_s1_8) + (1938449441493/1000000000000 : ℝ)*(sp_s1_9) + (452820688659/250000000000 : ℝ)*(sp_s1_13) + (65065639/1000000000000 : ℝ)*(sp_s1_14) + (198951/500000000000 : ℝ)*(sp_s1_23) + (514035009743/500000000000 : ℝ)*(f.failure) + (387689967879/200000000000 : ℝ)*(f.sum) + (144930632020929641/727016160000000000000000000000 : ℝ)*base63 + (90073837756407/547040000000000000000000000 : ℝ)*base65 + (37984456154019/84170000000000000000000000 : ℝ)*base66 + (368804925962671/1641120000000000000000000000 : ℝ)*base69 + (1199363847173572013/3086946720000000000000000000000 : ℝ)*base71 + (2671755622769/7053750000000000000000000 : ℝ)*base73 + (4293645997753/17720000000000000000000000 : ℝ)*base75 + (741604500503/1128600000000000000000000 : ℝ)*base77 + (1077060888363497/24998490000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (16641/50000000000000000 : ℝ)*base86 + (16641/50000000000000000 : ℝ)*base88 + (16641/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6919/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6919/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27622123784906849597864477/7913873825000000000000000000000 : ℝ) := by norm_num
    linear_combination (198501649403/250000000000 : ℝ)*(base7) + (973/250000000000 : ℝ)*(base24) + (1027/12500000000 : ℝ)*(base39) + (62001/500000000000 : ℝ)*(base49) + (1665046003089/1000000000000 : ℝ)*(major_s1_0) + (1665046003089/1000000000000 : ℝ)*(major_s1_1) + (1665046003089/1000000000000 : ℝ)*(major_s1_2) + (3838311/250000000000 : ℝ)*(sp_s1_8) + (930341447627/500000000000 : ℝ)*(sp_s1_14) + (1860667970521/1000000000000 : ℝ)*(sp_s1_15) + (1860683319873/1000000000000 : ℝ)*(sp_s1_16) + (1791536139573/1000000000000 : ℝ)*(sp_s1_20) + (13391/31250000000 : ℝ)*(sp_s1_21) + (5919059/250000000000 : ℝ)*(sp_s1_27) + (997553218197/1000000000000 : ℝ)*(f.failure) + (930341661883/500000000000 : ℝ)*(f.sum) + (427457703833366461/6058468000000000000000000000000 : ℝ)*base62 + (1428634192348469/2735200000000000000000000000 : ℝ)*base64 + (535148841217437/1052125000000000000000000000 : ℝ)*base66 + (652373635373823/2735200000000000000000000000 : ℝ)*base68 + (2737370075465127569/25724556000000000000000000000000 : ℝ)*base70 + (107707180092673/235125000000000000000000000 : ℝ)*base73 + (131770345829091/443000000000000000000000000 : ℝ)*base74 + (85600464588053/235125000000000000000000000 : ℝ)*base76 + (33386855687006677/208320750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (15861/100000000000000000 : ℝ)*base87 + (15861/100000000000000000 : ℝ)*base89 + (15861/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16649/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16649/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3350854644938677050176004347/379865943600000000000000000000000 : ℝ) := by norm_num
    linear_combination (78999121161/100000000000 : ℝ)*(base7) + (2039588049/15625000000 : ℝ)*(base40) + (319397/500000000000 : ℝ)*(base49) + (320737735057/200000000000 : ℝ)*(major_s1_0) + (320737735057/200000000000 : ℝ)*(major_s1_1) + (320737735057/200000000000 : ℝ)*(major_s1_2) + (2419251/200000000000 : ℝ)*(sp_s1_1) + (1683113/125000000000 : ℝ)*(sp_s1_2) + (24352413/500000000000 : ℝ)*(sp_s1_9) + (265947/250000000000 : ℝ)*(sp_s1_20) + (1777113179969/1000000000000 : ℝ)*(sp_s1_21) + (888550541857/500000000000 : ℝ)*(sp_s1_22) + (1777051010239/1000000000000 : ℝ)*(sp_s1_23) + (1750783300713/1000000000000 : ℝ)*(sp_s1_27) + (960793152891/1000000000000 : ℝ)*(f.failure) + (1777113179969/1000000000000 : ℝ)*(f.sum) + (757317484095441479/3635080800000000000000000000000 : ℝ)*base62 + (65538291717221/547040000000000000000000000 : ℝ)*base64 + (21586461124443/105212500000000000000000000 : ℝ)*base66 + (462750372425981/1641120000000000000000000000 : ℝ)*base68 + (6098284455429713869/15434733600000000000000000000000 : ℝ)*base71 + (17127583151267/35268750000000000000000000 : ℝ)*base72 + (12056438240263/88600000000000000000000000 : ℝ)*base74 + (83863284018341/282150000000000000000000000 : ℝ)*base77 + (85228622866858307/124992450000000000000000000000 : ℝ)*base78 + (4517/100000000000000000 : ℝ)*base86 + (4517/100000000000000000 : ℝ)*base88 + (4517/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((16929/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16929/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8417/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8417/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10257/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10257/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((34549/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34549/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6919/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6919/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16649/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16649/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312063_s1 p hpa hpb X hX hprev0

#print axioms solution

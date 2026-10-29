-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c324053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:57:54.925568+00:00
-- url     : https://prove2.me/submissions/172dc04e-4aba-43b0-8012-a3f8c8aad118

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
theorem collision_support_c324053_s1_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-974275641/5000000000 : ℝ)*x 0 + (2517674429/5000000000 : ℝ)*x 1 + (2541559529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (974275641/5000000000 : ℝ)^43 ≤ (670394225749/5000000000000 : ℝ)^35 := by
    have hnat : (974275641 : ℕ)^43*5000000000000^35 ≤ 670394225749^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974275641 5000000000 670394225749 5000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2517674429/5000000000 : ℝ)^43 ≤ (5380616629699/12500000000000 : ℝ)^35 := by
    have hnat : (2517674429 : ℕ)^43*12500000000000^35 ≤ 5380616629699^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517674429 5000000000 5380616629699 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541559529/5000000000 : ℝ)^43 ≤ (870943648551/2000000000000 : ℝ)^35 := by
    have hnat : (2541559529 : ℕ)^43*2000000000000^35 ≤ 870943648551^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541559529 5000000000 870943648551 2000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-974275641/5000000000 : ℝ), (2517674429/5000000000 : ℝ), (2541559529/5000000000 : ℝ)] ![(670394225749/5000000000000 : ℝ), (5380616629699/12500000000000 : ℝ), (870943648551/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-974275641/5000000000 : ℝ)|^43 ≤ (670394225749/5000000000000 : ℝ)^35
        have hw : |(-974275641/5000000000 : ℝ)|=(974275641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2517674429/5000000000 : ℝ)|^43 ≤ (5380616629699/12500000000000 : ℝ)^35
        have hw : |(2517674429/5000000000 : ℝ)|=(2517674429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541559529/5000000000 : ℝ)|^43 ≤ (870943648551/2000000000000 : ℝ)^35
        have hw : |(2541559529/5000000000 : ℝ)|=(2541559529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (894745319/2000000000 : ℝ)*x 0 + (6083103611/10000000000 : ℝ)*x 1 + (-1341807513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894745319/2000000000 : ℝ)^43 ≤ (37223949816171/100000000000000 : ℝ)^35 := by
    have hnat : (894745319 : ℕ)^43*100000000000000^35 ≤ 37223949816171^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894745319 2000000000 37223949816171 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6083103611/10000000000 : ℝ)^43 ≤ (54297821488979/100000000000000 : ℝ)^35 := by
    have hnat : (6083103611 : ℕ)^43*100000000000000^35 ≤ 54297821488979^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6083103611 10000000000 54297821488979 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1341807513/10000000000 : ℝ)^43 ≤ (1695645736147/20000000000000 : ℝ)^35 := by
    have hnat : (1341807513 : ℕ)^43*20000000000000^35 ≤ 1695645736147^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341807513 10000000000 1695645736147 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(894745319/2000000000 : ℝ), (6083103611/10000000000 : ℝ), (-1341807513/10000000000 : ℝ)] ![(37223949816171/100000000000000 : ℝ), (54297821488979/100000000000000 : ℝ), (1695645736147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(894745319/2000000000 : ℝ)|^43 ≤ (37223949816171/100000000000000 : ℝ)^35
        have hw : |(894745319/2000000000 : ℝ)|=(894745319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6083103611/10000000000 : ℝ)|^43 ≤ (54297821488979/100000000000000 : ℝ)^35
        have hw : |(6083103611/10000000000 : ℝ)|=(6083103611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1341807513/10000000000 : ℝ)|^43 ≤ (1695645736147/20000000000000 : ℝ)^35
        have hw : |(-1341807513/10000000000 : ℝ)|=(1341807513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7178084963/10000000000 : ℝ)*x 0 + (2366472363/10000000000 : ℝ)*x 1 + (2299689779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7178084963/10000000000 : ℝ)^43 ≤ (33271032429243/50000000000000 : ℝ)^35 := by
    have hnat : (7178084963 : ℕ)^43*50000000000000^35 ≤ 33271032429243^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7178084963 10000000000 33271032429243 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2366472363/10000000000 : ℝ)^43 ≤ (3404622021221/20000000000000 : ℝ)^35 := by
    have hnat : (2366472363 : ℕ)^43*20000000000000^35 ≤ 3404622021221^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366472363 10000000000 3404622021221 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2299689779/10000000000 : ℝ)^43 ≤ (4108706256473/25000000000000 : ℝ)^35 := by
    have hnat : (2299689779 : ℕ)^43*25000000000000^35 ≤ 4108706256473^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299689779 10000000000 4108706256473 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7178084963/10000000000 : ℝ), (2366472363/10000000000 : ℝ), (2299689779/10000000000 : ℝ)] ![(33271032429243/50000000000000 : ℝ), (3404622021221/20000000000000 : ℝ), (4108706256473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7178084963/10000000000 : ℝ)|^43 ≤ (33271032429243/50000000000000 : ℝ)^35
        have hw : |(7178084963/10000000000 : ℝ)|=(7178084963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2366472363/10000000000 : ℝ)|^43 ≤ (3404622021221/20000000000000 : ℝ)^35
        have hw : |(2366472363/10000000000 : ℝ)|=(2366472363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2299689779/10000000000 : ℝ)|^43 ≤ (4108706256473/25000000000000 : ℝ)^35
        have hw : |(2299689779/10000000000 : ℝ)|=(2299689779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-940661151/5000000000 : ℝ)*x 0 + (16089723/39062500 : ℝ)*x 1 + (6012734303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940661151/5000000000 : ℝ)^43 ≤ (401306545683/3125000000000 : ℝ)^35 := by
    have hnat : (940661151 : ℕ)^43*3125000000000^35 ≤ 401306545683^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940661151 5000000000 401306545683 3125000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16089723/39062500 : ℝ)^43 ≤ (33631032235127/100000000000000 : ℝ)^35 := by
    have hnat : (16089723 : ℕ)^43*100000000000000^35 ≤ 33631032235127^35*39062500^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16089723 39062500 33631032235127 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6012734303/10000000000 : ℝ)^43 ≤ (53527158287141/100000000000000 : ℝ)^35 := by
    have hnat : (6012734303 : ℕ)^43*100000000000000^35 ≤ 53527158287141^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6012734303 10000000000 53527158287141 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-940661151/5000000000 : ℝ), (16089723/39062500 : ℝ), (6012734303/10000000000 : ℝ)] ![(401306545683/3125000000000 : ℝ), (33631032235127/100000000000000 : ℝ), (53527158287141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-940661151/5000000000 : ℝ)|^43 ≤ (401306545683/3125000000000 : ℝ)^35
        have hw : |(-940661151/5000000000 : ℝ)|=(940661151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16089723/39062500 : ℝ)|^43 ≤ (33631032235127/100000000000000 : ℝ)^35
        have hw : |(16089723/39062500 : ℝ)|=(16089723/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6012734303/10000000000 : ℝ)|^43 ≤ (53527158287141/100000000000000 : ℝ)^35
        have hw : |(6012734303/10000000000 : ℝ)|=(6012734303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1039751299/2500000000 : ℝ)*x 0 + (-1077245887/10000000000 : ℝ)*x 1 + (6552831541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039751299/2500000000 : ℝ)^43 ≤ (17016543353407/50000000000000 : ℝ)^35 := by
    have hnat : (1039751299 : ℕ)^43*50000000000000^35 ≤ 17016543353407^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039751299 2500000000 17016543353407 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077245887/10000000000 : ℝ)^43 ≤ (404584912719/6250000000000 : ℝ)^35 := by
    have hnat : (1077245887 : ℕ)^43*6250000000000^35 ≤ 404584912719^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077245887 10000000000 404584912719 6250000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6552831541/10000000000 : ℝ)^43 ≤ (29746777341793/50000000000000 : ℝ)^35 := by
    have hnat : (6552831541 : ℕ)^43*50000000000000^35 ≤ 29746777341793^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6552831541 10000000000 29746777341793 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039751299/2500000000 : ℝ), (-1077245887/10000000000 : ℝ), (6552831541/10000000000 : ℝ)] ![(17016543353407/50000000000000 : ℝ), (404584912719/6250000000000 : ℝ), (29746777341793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039751299/2500000000 : ℝ)|^43 ≤ (17016543353407/50000000000000 : ℝ)^35
        have hw : |(1039751299/2500000000 : ℝ)|=(1039751299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1077245887/10000000000 : ℝ)|^43 ≤ (404584912719/6250000000000 : ℝ)^35
        have hw : |(-1077245887/10000000000 : ℝ)|=(1077245887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6552831541/10000000000 : ℝ)|^43 ≤ (29746777341793/50000000000000 : ℝ)^35
        have hw : |(6552831541/10000000000 : ℝ)|=(6552831541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2089936203/5000000000 : ℝ)*x 0 + (690966143/1000000000 : ℝ)*x 1 + (-5715441/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089936203/5000000000 : ℝ)^43 ≤ (1070093529041/3125000000000 : ℝ)^35 := by
    have hnat : (2089936203 : ℕ)^43*3125000000000^35 ≤ 1070093529041^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089936203 5000000000 1070093529041 3125000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (690966143/1000000000 : ℝ)^43 ≤ (15874541129211/25000000000000 : ℝ)^35 := by
    have hnat : (690966143 : ℕ)^43*25000000000000^35 ≤ 15874541129211^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690966143 1000000000 15874541129211 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5715441/125000000 : ℝ)^43 ≤ (2258842537531/100000000000000 : ℝ)^35 := by
    have hnat : (5715441 : ℕ)^43*100000000000000^35 ≤ 2258842537531^35*125000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5715441 125000000 2258842537531 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089936203/5000000000 : ℝ), (690966143/1000000000 : ℝ), (-5715441/125000000 : ℝ)] ![(1070093529041/3125000000000 : ℝ), (15874541129211/25000000000000 : ℝ), (2258842537531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089936203/5000000000 : ℝ)|^43 ≤ (1070093529041/3125000000000 : ℝ)^35
        have hw : |(2089936203/5000000000 : ℝ)|=(2089936203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(690966143/1000000000 : ℝ)|^43 ≤ (15874541129211/25000000000000 : ℝ)^35
        have hw : |(690966143/1000000000 : ℝ)|=(690966143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5715441/125000000 : ℝ)|^43 ≤ (2258842537531/100000000000000 : ℝ)^35
        have hw : |(-5715441/125000000 : ℝ)|=(5715441/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3469095523/5000000000 : ℝ)*x 0 + (938660529/2500000000 : ℝ)*x 1 + (1035338087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3469095523/5000000000 : ℝ)^43 ≤ (6382042378073/10000000000000 : ℝ)^35 := by
    have hnat : (3469095523 : ℕ)^43*10000000000000^35 ≤ 6382042378073^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3469095523 5000000000 6382042378073 10000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938660529/2500000000 : ℝ)^43 ≤ (3751777594337/12500000000000 : ℝ)^35 := by
    have hnat : (938660529 : ℕ)^43*12500000000000^35 ≤ 3751777594337^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938660529 2500000000 3751777594337 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035338087/10000000000 : ℝ)^43 ≤ (6165355450869/100000000000000 : ℝ)^35 := by
    have hnat : (1035338087 : ℕ)^43*100000000000000^35 ≤ 6165355450869^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035338087 10000000000 6165355450869 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3469095523/5000000000 : ℝ), (938660529/2500000000 : ℝ), (1035338087/10000000000 : ℝ)] ![(6382042378073/10000000000000 : ℝ), (3751777594337/12500000000000 : ℝ), (6165355450869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3469095523/5000000000 : ℝ)|^43 ≤ (6382042378073/10000000000000 : ℝ)^35
        have hw : |(3469095523/5000000000 : ℝ)|=(3469095523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(938660529/2500000000 : ℝ)|^43 ≤ (3751777594337/12500000000000 : ℝ)^35
        have hw : |(938660529/2500000000 : ℝ)|=(938660529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035338087/10000000000 : ℝ)|^43 ≤ (6165355450869/100000000000000 : ℝ)^35
        have hw : |(1035338087/10000000000 : ℝ)|=(1035338087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-127444153/1250000000 : ℝ)*x 0 + (4852614003/10000000000 : ℝ)*x 1 + (5947642991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127444153/1250000000 : ℝ)^43 ≤ (6050074702823/100000000000000 : ℝ)^35 := by
    have hnat : (127444153 : ℕ)^43*100000000000000^35 ≤ 6050074702823^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127444153 1250000000 6050074702823 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4852614003/10000000000 : ℝ)^43 ≤ (41133794592189/100000000000000 : ℝ)^35 := by
    have hnat : (4852614003 : ℕ)^43*100000000000000^35 ≤ 41133794592189^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4852614003 10000000000 41133794592189 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5947642991/10000000000 : ℝ)^43 ≤ (26408065342247/50000000000000 : ℝ)^35 := by
    have hnat : (5947642991 : ℕ)^43*50000000000000^35 ≤ 26408065342247^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5947642991 10000000000 26408065342247 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127444153/1250000000 : ℝ), (4852614003/10000000000 : ℝ), (5947642991/10000000000 : ℝ)] ![(6050074702823/100000000000000 : ℝ), (41133794592189/100000000000000 : ℝ), (26408065342247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127444153/1250000000 : ℝ)|^43 ≤ (6050074702823/100000000000000 : ℝ)^35
        have hw : |(-127444153/1250000000 : ℝ)|=(127444153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4852614003/10000000000 : ℝ)|^43 ≤ (41133794592189/100000000000000 : ℝ)^35
        have hw : |(4852614003/10000000000 : ℝ)|=(4852614003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5947642991/10000000000 : ℝ)|^43 ≤ (26408065342247/50000000000000 : ℝ)^35
        have hw : |(5947642991/10000000000 : ℝ)|=(5947642991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2065304857/5000000000 : ℝ)*x 0 + (-218437583/2000000000 : ℝ)*x 1 + (6568494871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065304857/5000000000 : ℝ)^43 ≤ (33747839151033/100000000000000 : ℝ)^35 := by
    have hnat : (2065304857 : ℕ)^43*100000000000000^35 ≤ 33747839151033^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065304857 5000000000 33747839151033 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218437583/2000000000 : ℝ)^43 ≤ (1645961341291/25000000000000 : ℝ)^35 := by
    have hnat : (218437583 : ℕ)^43*25000000000000^35 ≤ 1645961341291^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218437583 2000000000 1645961341291 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6568494871/10000000000 : ℝ)^43 ≤ (29834157731951/50000000000000 : ℝ)^35 := by
    have hnat : (6568494871 : ℕ)^43*50000000000000^35 ≤ 29834157731951^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6568494871 10000000000 29834157731951 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2065304857/5000000000 : ℝ), (-218437583/2000000000 : ℝ), (6568494871/10000000000 : ℝ)] ![(33747839151033/100000000000000 : ℝ), (1645961341291/25000000000000 : ℝ), (29834157731951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2065304857/5000000000 : ℝ)|^43 ≤ (33747839151033/100000000000000 : ℝ)^35
        have hw : |(2065304857/5000000000 : ℝ)|=(2065304857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-218437583/2000000000 : ℝ)|^43 ≤ (1645961341291/25000000000000 : ℝ)^35
        have hw : |(-218437583/2000000000 : ℝ)|=(218437583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6568494871/10000000000 : ℝ)|^43 ≤ (29834157731951/50000000000000 : ℝ)^35
        have hw : |(6568494871/10000000000 : ℝ)|=(6568494871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5447748801/10000000000 : ℝ)*x 0 + (5681171469/10000000000 : ℝ)*x 1 + (-522326363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5447748801/10000000000 : ℝ)^43 ≤ (5926985250919/12500000000000 : ℝ)^35 := by
    have hnat : (5447748801 : ℕ)^43*12500000000000^35 ≤ 5926985250919^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447748801 10000000000 5926985250919 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5681171469/10000000000 : ℝ)^43 ≤ (24962002426517/50000000000000 : ℝ)^35 := by
    have hnat : (5681171469 : ℕ)^43*50000000000000^35 ≤ 24962002426517^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681171469 10000000000 24962002426517 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522326363/10000000000 : ℝ)^43 ≤ (2660113121069/100000000000000 : ℝ)^35 := by
    have hnat : (522326363 : ℕ)^43*100000000000000^35 ≤ 2660113121069^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522326363 10000000000 2660113121069 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5447748801/10000000000 : ℝ), (5681171469/10000000000 : ℝ), (-522326363/10000000000 : ℝ)] ![(5926985250919/12500000000000 : ℝ), (24962002426517/50000000000000 : ℝ), (2660113121069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5447748801/10000000000 : ℝ)|^43 ≤ (5926985250919/12500000000000 : ℝ)^35
        have hw : |(5447748801/10000000000 : ℝ)|=(5447748801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5681171469/10000000000 : ℝ)|^43 ≤ (24962002426517/50000000000000 : ℝ)^35
        have hw : |(5681171469/10000000000 : ℝ)|=(5681171469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522326363/10000000000 : ℝ)|^43 ≤ (2660113121069/100000000000000 : ℝ)^35
        have hw : |(-522326363/10000000000 : ℝ)|=(522326363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8226785671/10000000000 : ℝ)*x 0 + (54800359/250000000 : ℝ)*x 1 + (197777459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8226785671/10000000000 : ℝ)^43 ≤ (39339082717949/50000000000000 : ℝ)^35 := by
    have hnat : (8226785671 : ℕ)^43*50000000000000^35 ≤ 39339082717949^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8226785671 10000000000 39339082717949 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54800359/250000000 : ℝ)^43 ≤ (3873638037437/25000000000000 : ℝ)^35 := by
    have hnat : (54800359 : ℕ)^43*25000000000000^35 ≤ 3873638037437^35*250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54800359 250000000 3873638037437 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197777459/2000000000 : ℝ)^43 ≤ (5827282398601/100000000000000 : ℝ)^35 := by
    have hnat : (197777459 : ℕ)^43*100000000000000^35 ≤ 5827282398601^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197777459 2000000000 5827282398601 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8226785671/10000000000 : ℝ), (54800359/250000000 : ℝ), (197777459/2000000000 : ℝ)] ![(39339082717949/50000000000000 : ℝ), (3873638037437/25000000000000 : ℝ), (5827282398601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8226785671/10000000000 : ℝ)|^43 ≤ (39339082717949/50000000000000 : ℝ)^35
        have hw : |(8226785671/10000000000 : ℝ)|=(8226785671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54800359/250000000 : ℝ)|^43 ≤ (3873638037437/25000000000000 : ℝ)^35
        have hw : |(54800359/250000000 : ℝ)|=(54800359/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197777459/2000000000 : ℝ)|^43 ≤ (5827282398601/100000000000000 : ℝ)^35
        have hw : |(197777459/2000000000 : ℝ)|=(197777459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-907198417/10000000000 : ℝ)*x 0 + (54602833/100000000 : ℝ)*x 1 + (5428343489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907198417/10000000000 : ℝ)^43 ≤ (2620793542893/50000000000000 : ℝ)^35 := by
    have hnat : (907198417 : ℕ)^43*50000000000000^35 ≤ 2620793542893^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907198417 10000000000 2620793542893 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54602833/100000000 : ℝ)^43 ≤ (23774975488001/50000000000000 : ℝ)^35 := by
    have hnat : (54602833 : ℕ)^43*50000000000000^35 ≤ 23774975488001^35*100000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54602833 100000000 23774975488001 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428343489/10000000000 : ℝ)^43 ≤ (47208461924483/100000000000000 : ℝ)^35 := by
    have hnat : (5428343489 : ℕ)^43*100000000000000^35 ≤ 47208461924483^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428343489 10000000000 47208461924483 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-907198417/10000000000 : ℝ), (54602833/100000000 : ℝ), (5428343489/10000000000 : ℝ)] ![(2620793542893/50000000000000 : ℝ), (23774975488001/50000000000000 : ℝ), (47208461924483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-907198417/10000000000 : ℝ)|^43 ≤ (2620793542893/50000000000000 : ℝ)^35
        have hw : |(-907198417/10000000000 : ℝ)|=(907198417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54602833/100000000 : ℝ)|^43 ≤ (23774975488001/50000000000000 : ℝ)^35
        have hw : |(54602833/100000000 : ℝ)|=(54602833/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428343489/10000000000 : ℝ)|^43 ≤ (47208461924483/100000000000000 : ℝ)^35
        have hw : |(5428343489/10000000000 : ℝ)|=(5428343489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5539235083/10000000000 : ℝ)*x 0 + (-643834403/10000000000 : ℝ)*x 1 + (5517653531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5539235083/10000000000 : ℝ)^43 ≤ (6049503932763/12500000000000 : ℝ)^35 := by
    have hnat : (5539235083 : ℕ)^43*12500000000000^35 ≤ 6049503932763^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5539235083 10000000000 6049503932763 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643834403/10000000000 : ℝ)^43 ≤ (3439489529519/100000000000000 : ℝ)^35 := by
    have hnat : (643834403 : ℕ)^43*100000000000000^35 ≤ 3439489529519^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643834403 10000000000 3439489529519 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5517653531/10000000000 : ℝ)^43 ≤ (1926579159607/4000000000000 : ℝ)^35 := by
    have hnat : (5517653531 : ℕ)^43*4000000000000^35 ≤ 1926579159607^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517653531 10000000000 1926579159607 4000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5539235083/10000000000 : ℝ), (-643834403/10000000000 : ℝ), (5517653531/10000000000 : ℝ)] ![(6049503932763/12500000000000 : ℝ), (3439489529519/100000000000000 : ℝ), (1926579159607/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5539235083/10000000000 : ℝ)|^43 ≤ (6049503932763/12500000000000 : ℝ)^35
        have hw : |(5539235083/10000000000 : ℝ)|=(5539235083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-643834403/10000000000 : ℝ)|^43 ≤ (3439489529519/100000000000000 : ℝ)^35
        have hw : |(-643834403/10000000000 : ℝ)|=(643834403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5517653531/10000000000 : ℝ)|^43 ≤ (1926579159607/4000000000000 : ℝ)^35
        have hw : |(5517653531/10000000000 : ℝ)|=(5517653531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4085401571/10000000000 : ℝ)*x 0 + (6770261321/10000000000 : ℝ)*x 1 + (-210312749/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4085401571/10000000000 : ℝ)^43 ≤ (16647312330921/50000000000000 : ℝ)^35 := by
    have hnat : (4085401571 : ℕ)^43*50000000000000^35 ≤ 16647312330921^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4085401571 10000000000 16647312330921 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6770261321/10000000000 : ℝ)^43 ≤ (61927945704403/100000000000000 : ℝ)^35 := by
    have hnat : (6770261321 : ℕ)^43*100000000000000^35 ≤ 61927945704403^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6770261321 10000000000 61927945704403 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210312749/2500000000 : ℝ)^43 ≤ (4777429621957/100000000000000 : ℝ)^35 := by
    have hnat : (210312749 : ℕ)^43*100000000000000^35 ≤ 4777429621957^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210312749 2500000000 4777429621957 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4085401571/10000000000 : ℝ), (6770261321/10000000000 : ℝ), (-210312749/2500000000 : ℝ)] ![(16647312330921/50000000000000 : ℝ), (61927945704403/100000000000000 : ℝ), (4777429621957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4085401571/10000000000 : ℝ)|^43 ≤ (16647312330921/50000000000000 : ℝ)^35
        have hw : |(4085401571/10000000000 : ℝ)|=(4085401571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6770261321/10000000000 : ℝ)|^43 ≤ (61927945704403/100000000000000 : ℝ)^35
        have hw : |(6770261321/10000000000 : ℝ)|=(6770261321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210312749/2500000000 : ℝ)|^43 ≤ (4777429621957/100000000000000 : ℝ)^35
        have hw : |(-210312749/2500000000 : ℝ)|=(210312749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324053_s1_s1_27 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4211374051/5000000000 : ℝ)*x 0 + (1475507327/10000000000 : ℝ)*x 1 + (183773949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211374051/5000000000 : ℝ)^43 ≤ (16197376586623/20000000000000 : ℝ)^35 := by
    have hnat : (4211374051 : ℕ)^43*20000000000000^35 ≤ 16197376586623^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211374051 5000000000 16197376586623 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1475507327/10000000000 : ℝ)^43 ≤ (381105400977/4000000000000 : ℝ)^35 := by
    have hnat : (1475507327 : ℕ)^43*4000000000000^35 ≤ 381105400977^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475507327 10000000000 381105400977 4000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183773949/1250000000 : ℝ)^43 ≤ (1897096405439/20000000000000 : ℝ)^35 := by
    have hnat : (183773949 : ℕ)^43*20000000000000^35 ≤ 1897096405439^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183773949 1250000000 1897096405439 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211374051/5000000000 : ℝ), (1475507327/10000000000 : ℝ), (183773949/1250000000 : ℝ)] ![(16197376586623/20000000000000 : ℝ), (381105400977/4000000000000 : ℝ), (1897096405439/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211374051/5000000000 : ℝ)|^43 ≤ (16197376586623/20000000000000 : ℝ)^35
        have hw : |(4211374051/5000000000 : ℝ)|=(4211374051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1475507327/10000000000 : ℝ)|^43 ≤ (381105400977/4000000000000 : ℝ)^35
        have hw : |(1475507327/10000000000 : ℝ)|=(1475507327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(183773949/1250000000 : ℝ)|^43 ≤ (1897096405439/20000000000000 : ℝ)^35
        have hw : |(183773949/1250000000 : ℝ)|=(183773949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324053_s1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((68197/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68197/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17081/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17081/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33393/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33393/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16219/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16219/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7767/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7767/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36921/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36921/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (68197/100000 : ℝ) ^ (21/4 : ℝ) ≤ (13405026271496803583/100000000000000000000 : ℝ) := by
    have hpowers : (68197/100000 : ℝ)^21 ≤ (13405026271496803583/100000000000000000000 : ℝ)^4 := by
      have hnat : (68197 : ℕ)^21*100000000000000000000^4 ≤ 13405026271496803583^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68197 100000 13405026271496803583 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68197/100000 : ℝ)) (X := (13405026271496803583/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (113405026271496803583/100000000000000000000 : ℝ) ≤ (1024250425526153/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (113405026271496803583/100000000000000000000 : ℝ)^4 ≤ (1024250425526153/1000000000000000 : ℝ)^21 := by
      have hnat : (113405026271496803583 : ℕ)^4*1000000000000000^21 ≤ 1024250425526153^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113405026271496803583 100000000000000000000 1024250425526153 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1024250425526153/1000000000000000 : ℝ)) (X := (113405026271496803583/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (63405026271496803583/50000000000000000000 : ℝ) ≤ (10462809558646147/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (63405026271496803583/50000000000000000000 : ℝ)^4 ≤ (10462809558646147/10000000000000000 : ℝ)^21 := by
      have hnat : (63405026271496803583 : ℕ)^4*10000000000000000^21 ≤ 10462809558646147^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63405026271496803583 50000000000000000000 10462809558646147 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10462809558646147/10000000000000000 : ℝ)) (X := (63405026271496803583/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(24250425526153/681970000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(220305303384617/6819700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (68197/100000 : ℝ)) (alpha := (24250425526153/681970000000000 : ℝ)) (beta := (220305303384617/6819700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (68197/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(24250425526153/681970000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(220305303384617/6819700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (17081/25000 : ℝ) ^ (21/4 : ℝ) ≤ (2707320904924604673/20000000000000000000 : ℝ) := by
    have hpowers : (17081/25000 : ℝ)^21 ≤ (2707320904924604673/20000000000000000000 : ℝ)^4 := by
      have hnat : (17081 : ℕ)^21*20000000000000000000^4 ≤ 2707320904924604673^4*25000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17081 25000 2707320904924604673 20000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17081/25000 : ℝ)) (X := (2707320904924604673/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (22707320904924604673/20000000000000000000 : ℝ) ≤ (5122383393816149/5000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (22707320904924604673/20000000000000000000 : ℝ)^4 ≤ (5122383393816149/5000000000000000 : ℝ)^21 := by
      have hnat : (22707320904924604673 : ℕ)^4*5000000000000000^21 ≤ 5122383393816149^21*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22707320904924604673 20000000000000000000 5122383393816149 5000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5122383393816149/5000000000000000 : ℝ)) (X := (22707320904924604673/20000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12707320904924604673/10000000000000000000 : ℝ) ≤ (2616735448284221/2500000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (12707320904924604673/10000000000000000000 : ℝ)^4 ≤ (2616735448284221/2500000000000000 : ℝ)^21 := by
      have hnat : (12707320904924604673 : ℕ)^4*2500000000000000^21 ≤ 2616735448284221^21*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12707320904924604673 10000000000000000000 2616735448284221 2500000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2616735448284221/2500000000000000 : ℝ)) (X := (12707320904924604673/10000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(122383393816149/3416200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(111087502752293/3416200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (17081/25000 : ℝ)) (alpha := (122383393816149/3416200000000000 : ℝ)) (beta := (111087502752293/3416200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (17081/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(122383393816149/3416200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(111087502752293/3416200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (33393/50000 : ℝ) ^ (21/4 : ℝ) ≤ (6005767677758980179/50000000000000000000 : ℝ) := by
    have hpowers : (33393/50000 : ℝ)^21 ≤ (6005767677758980179/50000000000000000000 : ℝ)^4 := by
      have hnat : (33393 : ℕ)^21*50000000000000000000^4 ≤ 6005767677758980179^4*50000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33393 50000 6005767677758980179 50000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33393/50000 : ℝ)) (X := (6005767677758980179/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (56005767677758980179/50000000000000000000 : ℝ) ≤ (2554602834171711/2500000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (56005767677758980179/50000000000000000000 : ℝ)^4 ≤ (2554602834171711/2500000000000000 : ℝ)^21 := by
      have hnat : (56005767677758980179 : ℕ)^4*2500000000000000^21 ≤ 2554602834171711^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56005767677758980179 50000000000000000000 2554602834171711 2500000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2554602834171711/2500000000000000 : ℝ)) (X := (56005767677758980179/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (31005767677758980179/25000000000000000000 : ℝ) ≤ (1302326894106349/1250000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (31005767677758980179/25000000000000000000 : ℝ)^4 ≤ (1302326894106349/1250000000000000 : ℝ)^21 := by
      have hnat : (31005767677758980179 : ℕ)^4*1250000000000000^21 ≤ 1302326894106349^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31005767677758980179 25000000000000000000 1302326894106349 1250000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1302326894106349/1250000000000000 : ℝ)) (X := (31005767677758980179/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(54602834171711/1669650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(50050954040987/1669650000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (33393/50000 : ℝ)) (alpha := (54602834171711/1669650000000000 : ℝ)) (beta := (50050954040987/1669650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (33393/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(54602834171711/1669650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(50050954040987/1669650000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-974275641/5000000000 : ℝ)*X 0 0+(2517674429/5000000000 : ℝ)*X 0 1+(2541559529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((894745319/2000000000 : ℝ)*X 2 0+(6083103611/10000000000 : ℝ)*X 2 1+(-1341807513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((7178084963/10000000000 : ℝ)*X 0 0+(2366472363/10000000000 : ℝ)*X 0 1+(2299689779/10000000000 : ℝ)*X 0 2+(7178084963/10000000000 : ℝ)*X 1 0+(2366472363/10000000000 : ℝ)*X 1 1+(2299689779/10000000000 : ℝ)*X 1 2+(7178084963/10000000000 : ℝ)*X 2 0+(2366472363/10000000000 : ℝ)*X 2 1+(2299689779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-940661151/5000000000 : ℝ)*X 0 0+(16089723/39062500 : ℝ)*X 0 1+(6012734303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1039751299/2500000000 : ℝ)*X 1 0+(-1077245887/10000000000 : ℝ)*X 1 1+(6552831541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2089936203/5000000000 : ℝ)*X 2 0+(690966143/1000000000 : ℝ)*X 2 1+(-5715441/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3469095523/5000000000 : ℝ)*X 0 0+(938660529/2500000000 : ℝ)*X 0 1+(1035338087/10000000000 : ℝ)*X 0 2+(3469095523/5000000000 : ℝ)*X 1 0+(938660529/2500000000 : ℝ)*X 1 1+(1035338087/10000000000 : ℝ)*X 1 2+(3469095523/5000000000 : ℝ)*X 2 0+(938660529/2500000000 : ℝ)*X 2 1+(1035338087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-127444153/1250000000 : ℝ)*X 0 0+(4852614003/10000000000 : ℝ)*X 0 1+(5947642991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2065304857/5000000000 : ℝ)*X 1 0+(-218437583/2000000000 : ℝ)*X 1 1+(6568494871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5447748801/10000000000 : ℝ)*X 2 0+(5681171469/10000000000 : ℝ)*X 2 1+(-522326363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((8226785671/10000000000 : ℝ)*X 0 0+(54800359/250000000 : ℝ)*X 0 1+(197777459/2000000000 : ℝ)*X 0 2+(8226785671/10000000000 : ℝ)*X 1 0+(54800359/250000000 : ℝ)*X 1 1+(197777459/2000000000 : ℝ)*X 1 2+(8226785671/10000000000 : ℝ)*X 2 0+(54800359/250000000 : ℝ)*X 2 1+(197777459/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-907198417/10000000000 : ℝ)*X 0 0+(54602833/100000000 : ℝ)*X 0 1+(5428343489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5539235083/10000000000 : ℝ)*X 1 0+(-643834403/10000000000 : ℝ)*X 1 1+(5517653531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4085401571/10000000000 : ℝ)*X 2 0+(6770261321/10000000000 : ℝ)*X 2 1+(-210312749/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4211374051/5000000000 : ℝ)*X 0 0+(1475507327/10000000000 : ℝ)*X 0 1+(183773949/1250000000 : ℝ)*X 0 2+(4211374051/5000000000 : ℝ)*X 1 0+(1475507327/10000000000 : ℝ)*X 1 1+(183773949/1250000000 : ℝ)*X 1 2+(4211374051/5000000000 : ℝ)*X 2 0+(1475507327/10000000000 : ℝ)*X 2 1+(183773949/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((16219/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16219/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (486580200218782553949/27550000000000000000000000 : ℝ) := by norm_num
    linear_combination (155713/1000000000000 : ℝ)*(base8) + (852406623/10000000000 : ℝ)*(base49) + (439513155223/500000000000 : ℝ)*(base59) + (5340324966579/1000000000000 : ℝ)*(major_s1_0) + (5340324966579/1000000000000 : ℝ)*(major_s1_1) + (5340324966579/1000000000000 : ℝ)*(major_s1_2) + (139716717/1000000000000 : ℝ)*(sp_s1_0) + (12195413/1000000000000 : ℝ)*(sp_s1_6) + (3993616713597/500000000000 : ℝ)*(sp_s1_7) + (7985535861391/1000000000000 : ℝ)*(sp_s1_8) + (499183784067/62500000000 : ℝ)*(sp_s1_9) + (16832865943/6250000000 : ℝ)*(sp_s1_13) + (1837438233/1000000000000 : ℝ)*(sp_s1_15) + (432754551/1000000000000 : ℝ)*(sp_s1_23) + (2693270746293/1000000000000 : ℝ)*(f.failure) + (7987373299623/1000000000000 : ℝ)*(f.sum) + (92521960623269323/1226636200000000000000000000000 : ℝ)*base63 + (14360400983587/278275000000000000000000000 : ℝ)*base65 + (31805178492363/110200000000000000000000000 : ℝ)*base67 + (40386104242953/139137500000000000000000000 : ℝ)*base68 + (300581377313240787/37955040350000000000000000000000 : ℝ)*base70 + (1315463456683927/6819700000000000000000000000 : ℝ)*base72 + (13945312560001/110200000000000000000000000 : ℝ)*base75 + (289058858618077/681970000000000000000000000 : ℝ)*base77 + (1341973881129841857/7515309400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (15303/25000000000000000 : ℝ)*base87 + (15303/25000000000000000 : ℝ)*base89 + (15303/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7767/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7767/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3790883029812316825435067/1000676900000000000000000000000 : ℝ) := by norm_num
    linear_combination (88843/500000000000 : ℝ)*(base39) + (144610177767/1000000000000 : ℝ)*(base49) + (2352824893/7812500000 : ℝ)*(base59) + (5157842235029/1000000000000 : ℝ)*(major_s1_0) + (5157842235029/1000000000000 : ℝ)*(major_s1_1) + (5157842235029/1000000000000 : ℝ)*(major_s1_2) + (5421143/1000000000000 : ℝ)*(sp_s1_2) + (220163/200000000000 : ℝ)*(sp_s1_6) + (8339609/500000000000 : ℝ)*(sp_s1_7) + (482151673341/62500000000 : ℝ)*(sp_s1_14) + (3857221726337/500000000000 : ℝ)*(sp_s1_15) + (7714438031531/1000000000000 : ℝ)*(sp_s1_16) + (520243653763/200000000000 : ℝ)*(sp_s1_20) + (20384979/1000000000000 : ℝ)*(sp_s1_27) + (2601239754609/1000000000000 : ℝ)*(f.failure) + (3857221726337/500000000000 : ℝ)*(f.sum) + (268622459713413191/6004061400000000000000000000000 : ℝ)*base63 + (300169283183927/1669650000000000000000000000 : ℝ)*base65 + (26262402368797/179800000000000000000000000 : ℝ)*base67 + (227269054660241/1669650000000000000000000000 : ℝ)*base68 + (21715591919141954917/56932560525000000000000000000000 : ℝ)*base71 + (2033369388267147/6819700000000000000000000000 : ℝ)*base72 + (31805453578461/179800000000000000000000000 : ℝ)*base74 + (96663851854193/681970000000000000000000000 : ℝ)*base76 + (1682937439667506343/12261820600000000000000000000000 : ℝ)*base79 + (2261/25000000000000000 : ℝ)*base86 + (2261/25000000000000000 : ℝ)*base88 + (2261/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36921/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36921/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3812792229246198850958379087013/324155022109175000000000000000000000 : ℝ) := by norm_num
    linear_combination (233331731591/1000000000000 : ℝ)*(base40) + (560869/125000000000 : ℝ)*(base49) + (357841092251/1000000000000 : ℝ)*(base59) + (4533789312607/1000000000000 : ℝ)*(major_s1_0) + (4533789312607/1000000000000 : ℝ)*(major_s1_1) + (4533789312607/1000000000000 : ℝ)*(major_s1_2) + (1225519/50000000000 : ℝ)*(sp_s1_0) + (6582933/250000000000 : ℝ)*(sp_s1_2) + (1652617/62500000000 : ℝ)*(sp_s1_16) + (164117519/1000000000000 : ℝ)*(sp_s1_20) + (6781037256771/1000000000000 : ℝ)*(sp_s1_21) + (135621235343/20000000000 : ℝ)*(sp_s1_22) + (6781008993547/1000000000000 : ℝ)*(sp_s1_23) + (2286348819787/1000000000000 : ℝ)*(sp_s1_27) + (1143256468653/500000000000 : ℝ)*(f.failure) + (135621235343/20000000000 : ℝ)*(f.sum) + (9352620007993534913/114077166600000000000000000000000 : ℝ)*base62 + (925377712688797/834825000000000000000000000 : ℝ)*base64 + (3051710436848011/3416200000000000000000000000 : ℝ)*base66 + (93679109918921/208706250000000000000000000 : ℝ)*base68 + (15791853276483616447/113865121050000000000000000000000 : ℝ)*base71 + (5432670018711711/6819700000000000000000000000 : ℝ)*base72 + (3233257211082197/3416200000000000000000000000 : ℝ)*base74 + (287438873670341/681970000000000000000000000 : ℝ)*base76 + (121088688340426317869/232974591400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (10363/12500000000000000 : ℝ)*base87 + (10363/12500000000000000 : ℝ)*base89 + (10363/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((68197/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68197/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17081/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17081/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33393/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(33393/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16219/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16219/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7767/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7767/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36921/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36921/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c324053_s1 p hpa hpb X hX hprev0

#print axioms solution

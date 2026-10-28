-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302013_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:13:53.838782+00:00
-- url     : https://prove2.me/submissions/c7067533-d9e9-4f0f-8bff-681fadf9d10d

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
theorem collision_support_c302013_s1_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1620510681/2500000000 : ℝ)*x 0 + (146669229/500000000 : ℝ)*x 1 + (3316402329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1620510681/2500000000 : ℝ)^67 ≤ (2828857778027/5000000000000 : ℝ)^51 := by
    have hnat : (1620510681 : ℕ)^67*5000000000000^51 ≤ 2828857778027^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620510681 2500000000 2828857778027 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146669229/500000000 : ℝ)^67 ≤ (2495623678661/12500000000000 : ℝ)^51 := by
    have hnat : (146669229 : ℕ)^67*12500000000000^51 ≤ 2495623678661^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146669229 500000000 2495623678661 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3316402329/10000000000 : ℝ)^67 ≤ (11728927498917/50000000000000 : ℝ)^51 := by
    have hnat : (3316402329 : ℕ)^67*50000000000000^51 ≤ 11728927498917^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3316402329 10000000000 11728927498917 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1620510681/2500000000 : ℝ), (146669229/500000000 : ℝ), (3316402329/10000000000 : ℝ)] ![(2828857778027/5000000000000 : ℝ), (2495623678661/12500000000000 : ℝ), (11728927498917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1620510681/2500000000 : ℝ)|^67 ≤ (2828857778027/5000000000000 : ℝ)^51
        have hw : |(1620510681/2500000000 : ℝ)|=(1620510681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146669229/500000000 : ℝ)|^67 ≤ (2495623678661/12500000000000 : ℝ)^51
        have hw : |(146669229/500000000 : ℝ)|=(146669229/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3316402329/10000000000 : ℝ)|^67 ≤ (11728927498917/50000000000000 : ℝ)^51
        have hw : |(3316402329/10000000000 : ℝ)|=(3316402329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (811108727/2000000000 : ℝ)*x 0 + (-408539523/1000000000 : ℝ)*x 1 + (-4844632399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811108727/2000000000 : ℝ)^67 ≤ (6111025263957/20000000000000 : ℝ)^51 := by
    have hnat : (811108727 : ℕ)^67*20000000000000^51 ≤ 6111025263957^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811108727 2000000000 6111025263957 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408539523/1000000000 : ℝ)^67 ≤ (30850932665681/100000000000000 : ℝ)^51 := by
    have hnat : (408539523 : ℕ)^67*100000000000000^51 ≤ 30850932665681^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408539523 1000000000 30850932665681 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4844632399/10000000000 : ℝ)^67 ≤ (1929697050103/5000000000000 : ℝ)^51 := by
    have hnat : (4844632399 : ℕ)^67*5000000000000^51 ≤ 1929697050103^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844632399 10000000000 1929697050103 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(811108727/2000000000 : ℝ), (-408539523/1000000000 : ℝ), (-4844632399/10000000000 : ℝ)] ![(6111025263957/20000000000000 : ℝ), (30850932665681/100000000000000 : ℝ), (1929697050103/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(811108727/2000000000 : ℝ)|^67 ≤ (6111025263957/20000000000000 : ℝ)^51
        have hw : |(811108727/2000000000 : ℝ)|=(811108727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408539523/1000000000 : ℝ)|^67 ≤ (30850932665681/100000000000000 : ℝ)^51
        have hw : |(-408539523/1000000000 : ℝ)|=(408539523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4844632399/10000000000 : ℝ)|^67 ≤ (1929697050103/5000000000000 : ℝ)^51
        have hw : |(-4844632399/10000000000 : ℝ)|=(4844632399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1472868733/5000000000 : ℝ)*x 0 + (-2772252107/10000000000 : ℝ)*x 1 + (6897451159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1472868733/5000000000 : ℝ)^67 ≤ (1003775710371/5000000000000 : ℝ)^51 := by
    have hnat : (1472868733 : ℕ)^67*5000000000000^51 ≤ 1003775710371^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472868733 5000000000 1003775710371 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2772252107/10000000000 : ℝ)^67 ≤ (18536816248313/100000000000000 : ℝ)^51 := by
    have hnat : (2772252107 : ℕ)^67*100000000000000^51 ≤ 18536816248313^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772252107 10000000000 18536816248313 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6897451159/10000000000 : ℝ)^67 ≤ (6138766953171/10000000000000 : ℝ)^51 := by
    have hnat : (6897451159 : ℕ)^67*10000000000000^51 ≤ 6138766953171^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6897451159 10000000000 6138766953171 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1472868733/5000000000 : ℝ), (-2772252107/10000000000 : ℝ), (6897451159/10000000000 : ℝ)] ![(1003775710371/5000000000000 : ℝ), (18536816248313/100000000000000 : ℝ), (6138766953171/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1472868733/5000000000 : ℝ)|^67 ≤ (1003775710371/5000000000000 : ℝ)^51
        have hw : |(1472868733/5000000000 : ℝ)|=(1472868733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2772252107/10000000000 : ℝ)|^67 ≤ (18536816248313/100000000000000 : ℝ)^51
        have hw : |(-2772252107/10000000000 : ℝ)|=(2772252107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6897451159/10000000000 : ℝ)|^67 ≤ (6138766953171/10000000000000 : ℝ)^51
        have hw : |(6897451159/10000000000 : ℝ)|=(6897451159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2343903409/10000000000 : ℝ)*x 0 + (-3746331129/5000000000 : ℝ)*x 1 + (2559617851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2343903409/10000000000 : ℝ)^67 ≤ (7434362643503/50000000000000 : ℝ)^51 := by
    have hnat : (2343903409 : ℕ)^67*50000000000000^51 ≤ 7434362643503^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2343903409 10000000000 7434362643503 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3746331129/5000000000 : ℝ)^67 ≤ (68439420474803/100000000000000 : ℝ)^51 := by
    have hnat : (3746331129 : ℕ)^67*100000000000000^51 ≤ 68439420474803^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3746331129 5000000000 68439420474803 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2559617851/10000000000 : ℝ)^67 ≤ (16691854214703/100000000000000 : ℝ)^51 := by
    have hnat : (2559617851 : ℕ)^67*100000000000000^51 ≤ 16691854214703^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559617851 10000000000 16691854214703 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2343903409/10000000000 : ℝ), (-3746331129/5000000000 : ℝ), (2559617851/10000000000 : ℝ)] ![(7434362643503/50000000000000 : ℝ), (68439420474803/100000000000000 : ℝ), (16691854214703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2343903409/10000000000 : ℝ)|^67 ≤ (7434362643503/50000000000000 : ℝ)^51
        have hw : |(-2343903409/10000000000 : ℝ)|=(2343903409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3746331129/5000000000 : ℝ)|^67 ≤ (68439420474803/100000000000000 : ℝ)^51
        have hw : |(-3746331129/5000000000 : ℝ)|=(3746331129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2559617851/10000000000 : ℝ)|^67 ≤ (16691854214703/100000000000000 : ℝ)^51
        have hw : |(2559617851/10000000000 : ℝ)|=(2559617851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6435947391/10000000000 : ℝ)*x 0 + (756197173/2500000000 : ℝ)*x 1 + (3284793467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6435947391/10000000000 : ℝ)^67 ≤ (3503074398001/6250000000000 : ℝ)^51 := by
    have hnat : (6435947391 : ℕ)^67*6250000000000^51 ≤ 3503074398001^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6435947391 10000000000 3503074398001 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (756197173/2500000000 : ℝ)^67 ≤ (4157247047457/20000000000000 : ℝ)^51 := by
    have hnat : (756197173 : ℕ)^67*20000000000000^51 ≤ 4157247047457^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756197173 2500000000 4157247047457 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3284793467/10000000000 : ℝ)^67 ≤ (23164574379657/100000000000000 : ℝ)^51 := by
    have hnat : (3284793467 : ℕ)^67*100000000000000^51 ≤ 23164574379657^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3284793467 10000000000 23164574379657 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6435947391/10000000000 : ℝ), (756197173/2500000000 : ℝ), (3284793467/10000000000 : ℝ)] ![(3503074398001/6250000000000 : ℝ), (4157247047457/20000000000000 : ℝ), (23164574379657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6435947391/10000000000 : ℝ)|^67 ≤ (3503074398001/6250000000000 : ℝ)^51
        have hw : |(6435947391/10000000000 : ℝ)|=(6435947391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(756197173/2500000000 : ℝ)|^67 ≤ (4157247047457/20000000000000 : ℝ)^51
        have hw : |(756197173/2500000000 : ℝ)|=(756197173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3284793467/10000000000 : ℝ)|^67 ≤ (23164574379657/100000000000000 : ℝ)^51
        have hw : |(3284793467/10000000000 : ℝ)|=(3284793467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4118530987/10000000000 : ℝ)*x 0 + (-4053107893/10000000000 : ℝ)*x 1 + (-1203864487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4118530987/10000000000 : ℝ)^67 ≤ (31180077403447/100000000000000 : ℝ)^51 := by
    have hnat : (4118530987 : ℕ)^67*100000000000000^51 ≤ 31180077403447^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118530987 10000000000 31180077403447 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4053107893/10000000000 : ℝ)^67 ≤ (30531020051061/100000000000000 : ℝ)^51 := by
    have hnat : (4053107893 : ℕ)^67*100000000000000^51 ≤ 30531020051061^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053107893 10000000000 30531020051061 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203864487/2500000000 : ℝ)^67 ≤ (19144451267513/50000000000000 : ℝ)^51 := by
    have hnat : (1203864487 : ℕ)^67*50000000000000^51 ≤ 19144451267513^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203864487 2500000000 19144451267513 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4118530987/10000000000 : ℝ), (-4053107893/10000000000 : ℝ), (-1203864487/2500000000 : ℝ)] ![(31180077403447/100000000000000 : ℝ), (30531020051061/100000000000000 : ℝ), (19144451267513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4118530987/10000000000 : ℝ)|^67 ≤ (31180077403447/100000000000000 : ℝ)^51
        have hw : |(4118530987/10000000000 : ℝ)|=(4118530987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4053107893/10000000000 : ℝ)|^67 ≤ (30531020051061/100000000000000 : ℝ)^51
        have hw : |(-4053107893/10000000000 : ℝ)|=(4053107893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1203864487/2500000000 : ℝ)|^67 ≤ (19144451267513/50000000000000 : ℝ)^51
        have hw : |(-1203864487/2500000000 : ℝ)|=(1203864487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (407909137/2000000000 : ℝ)*x 0 + (-934754843/10000000000 : ℝ)*x 1 + (4345608263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407909137/2000000000 : ℝ)^67 ≤ (12385583657971/100000000000000 : ℝ)^51 := by
    have hnat : (407909137 : ℕ)^67*100000000000000^51 ≤ 12385583657971^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407909137 2000000000 12385583657971 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934754843/10000000000 : ℝ)^67 ≤ (888810872377/20000000000000 : ℝ)^51 := by
    have hnat : (934754843 : ℕ)^67*20000000000000^51 ≤ 888810872377^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934754843 10000000000 888810872377 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4345608263/5000000000 : ℝ)^67 ≤ (16634072393759/20000000000000 : ℝ)^51 := by
    have hnat : (4345608263 : ℕ)^67*20000000000000^51 ≤ 16634072393759^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345608263 5000000000 16634072393759 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(407909137/2000000000 : ℝ), (-934754843/10000000000 : ℝ), (4345608263/5000000000 : ℝ)] ![(12385583657971/100000000000000 : ℝ), (888810872377/20000000000000 : ℝ), (16634072393759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(407909137/2000000000 : ℝ)|^67 ≤ (12385583657971/100000000000000 : ℝ)^51
        have hw : |(407909137/2000000000 : ℝ)|=(407909137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-934754843/10000000000 : ℝ)|^67 ≤ (888810872377/20000000000000 : ℝ)^51
        have hw : |(-934754843/10000000000 : ℝ)|=(934754843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4345608263/5000000000 : ℝ)|^67 ≤ (16634072393759/20000000000000 : ℝ)^51
        have hw : |(4345608263/5000000000 : ℝ)|=(4345608263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2970952497/10000000000 : ℝ)*x 0 + (-6463941727/10000000000 : ℝ)*x 1 + (3302498259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2970952497/10000000000 : ℝ)^67 ≤ (20301571426573/100000000000000 : ℝ)^51 := by
    have hnat : (2970952497 : ℕ)^67*100000000000000^51 ≤ 20301571426573^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2970952497 10000000000 20301571426573 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6463941727/10000000000 : ℝ)^67 ≤ (56369690033879/100000000000000 : ℝ)^51 := by
    have hnat : (6463941727 : ℕ)^67*100000000000000^51 ≤ 56369690033879^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6463941727 10000000000 56369690033879 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3302498259/10000000000 : ℝ)^67 ≤ (5832184629587/25000000000000 : ℝ)^51 := by
    have hnat : (3302498259 : ℕ)^67*25000000000000^51 ≤ 5832184629587^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3302498259 10000000000 5832184629587 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2970952497/10000000000 : ℝ), (-6463941727/10000000000 : ℝ), (3302498259/10000000000 : ℝ)] ![(20301571426573/100000000000000 : ℝ), (56369690033879/100000000000000 : ℝ), (5832184629587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2970952497/10000000000 : ℝ)|^67 ≤ (20301571426573/100000000000000 : ℝ)^51
        have hw : |(-2970952497/10000000000 : ℝ)|=(2970952497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6463941727/10000000000 : ℝ)|^67 ≤ (56369690033879/100000000000000 : ℝ)^51
        have hw : |(-6463941727/10000000000 : ℝ)|=(6463941727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3302498259/10000000000 : ℝ)|^67 ≤ (5832184629587/25000000000000 : ℝ)^51
        have hw : |(3302498259/10000000000 : ℝ)|=(3302498259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7516759089/10000000000 : ℝ)*x 0 + (1183715787/5000000000 : ℝ)*x 1 + (2502726223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7516759089/10000000000 : ℝ)^67 ≤ (68728723917491/100000000000000 : ℝ)^51 := by
    have hnat : (7516759089 : ℕ)^67*100000000000000^51 ≤ 68728723917491^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7516759089 10000000000 68728723917491 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1183715787/5000000000 : ℝ)^67 ≤ (3766277587053/25000000000000 : ℝ)^51 := by
    have hnat : (1183715787 : ℕ)^67*25000000000000^51 ≤ 3766277587053^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183715787 5000000000 3766277587053 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2502726223/10000000000 : ℝ)^67 ≤ (16206165719161/100000000000000 : ℝ)^51 := by
    have hnat : (2502726223 : ℕ)^67*100000000000000^51 ≤ 16206165719161^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502726223 10000000000 16206165719161 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7516759089/10000000000 : ℝ), (1183715787/5000000000 : ℝ), (2502726223/10000000000 : ℝ)] ![(68728723917491/100000000000000 : ℝ), (3766277587053/25000000000000 : ℝ), (16206165719161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7516759089/10000000000 : ℝ)|^67 ≤ (68728723917491/100000000000000 : ℝ)^51
        have hw : |(7516759089/10000000000 : ℝ)|=(7516759089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1183715787/5000000000 : ℝ)|^67 ≤ (3766277587053/25000000000000 : ℝ)^51
        have hw : |(1183715787/5000000000 : ℝ)|=(1183715787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2502726223/10000000000 : ℝ)|^67 ≤ (16206165719161/100000000000000 : ℝ)^51
        have hw : |(2502726223/10000000000 : ℝ)|=(2502726223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3861894149/10000000000 : ℝ)*x 0 + (-432464327/1000000000 : ℝ)*x 1 + (-4797471009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3861894149/10000000000 : ℝ)^67 ≤ (5730586916681/20000000000000 : ℝ)^51 := by
    have hnat : (3861894149 : ℕ)^67*20000000000000^51 ≤ 5730586916681^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3861894149 10000000000 5730586916681 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432464327/1000000000 : ℝ)^67 ≤ (33245939893797/100000000000000 : ℝ)^51 := by
    have hnat : (432464327 : ℕ)^67*100000000000000^51 ≤ 33245939893797^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432464327 1000000000 33245939893797 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4797471009/10000000000 : ℝ)^67 ≤ (952528137717/2500000000000 : ℝ)^51 := by
    have hnat : (4797471009 : ℕ)^67*2500000000000^51 ≤ 952528137717^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4797471009 10000000000 952528137717 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3861894149/10000000000 : ℝ), (-432464327/1000000000 : ℝ), (-4797471009/10000000000 : ℝ)] ![(5730586916681/20000000000000 : ℝ), (33245939893797/100000000000000 : ℝ), (952528137717/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3861894149/10000000000 : ℝ)|^67 ≤ (5730586916681/20000000000000 : ℝ)^51
        have hw : |(3861894149/10000000000 : ℝ)|=(3861894149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-432464327/1000000000 : ℝ)|^67 ≤ (33245939893797/100000000000000 : ℝ)^51
        have hw : |(-432464327/1000000000 : ℝ)|=(432464327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4797471009/10000000000 : ℝ)|^67 ≤ (952528137717/2500000000000 : ℝ)^51
        have hw : |(-4797471009/10000000000 : ℝ)|=(4797471009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (686496143/5000000000 : ℝ)*x 0 + (-366856557/2500000000 : ℝ)*x 1 + (8804614371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (686496143/5000000000 : ℝ)^67 ≤ (7364319097229/100000000000000 : ℝ)^51 := by
    have hnat : (686496143 : ℕ)^67*100000000000000^51 ≤ 7364319097229^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686496143 5000000000 7364319097229 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366856557/2500000000 : ℝ)^67 ≤ (8036810656221/100000000000000 : ℝ)^51 := by
    have hnat : (366856557 : ℕ)^67*100000000000000^51 ≤ 8036810656221^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366856557 2500000000 8036810656221 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8804614371/10000000000 : ℝ)^67 ≤ (21149717559029/25000000000000 : ℝ)^51 := by
    have hnat : (8804614371 : ℕ)^67*25000000000000^51 ≤ 21149717559029^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8804614371 10000000000 21149717559029 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(686496143/5000000000 : ℝ), (-366856557/2500000000 : ℝ), (8804614371/10000000000 : ℝ)] ![(7364319097229/100000000000000 : ℝ), (8036810656221/100000000000000 : ℝ), (21149717559029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(686496143/5000000000 : ℝ)|^67 ≤ (7364319097229/100000000000000 : ℝ)^51
        have hw : |(686496143/5000000000 : ℝ)|=(686496143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366856557/2500000000 : ℝ)|^67 ≤ (8036810656221/100000000000000 : ℝ)^51
        have hw : |(-366856557/2500000000 : ℝ)|=(366856557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8804614371/10000000000 : ℝ)|^67 ≤ (21149717559029/25000000000000 : ℝ)^51
        have hw : |(8804614371/10000000000 : ℝ)|=(8804614371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-345571463/2000000000 : ℝ)*x 0 + (-7743156337/10000000000 : ℝ)*x 1 + (694241641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (345571463/2000000000 : ℝ)^67 ≤ (4980405050993/50000000000000 : ℝ)^51 := by
    have hnat : (345571463 : ℕ)^67*50000000000000^51 ≤ 4980405050993^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345571463 2000000000 4980405050993 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7743156337/10000000000 : ℝ)^67 ≤ (71460949400511/100000000000000 : ℝ)^51 := by
    have hnat : (7743156337 : ℕ)^67*100000000000000^51 ≤ 71460949400511^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7743156337 10000000000 71460949400511 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694241641/2500000000 : ℝ)^67 ≤ (18578240485483/100000000000000 : ℝ)^51 := by
    have hnat : (694241641 : ℕ)^67*100000000000000^51 ≤ 18578240485483^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694241641 2500000000 18578240485483 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-345571463/2000000000 : ℝ), (-7743156337/10000000000 : ℝ), (694241641/2500000000 : ℝ)] ![(4980405050993/50000000000000 : ℝ), (71460949400511/100000000000000 : ℝ), (18578240485483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-345571463/2000000000 : ℝ)|^67 ≤ (4980405050993/50000000000000 : ℝ)^51
        have hw : |(-345571463/2000000000 : ℝ)|=(345571463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7743156337/10000000000 : ℝ)|^67 ≤ (71460949400511/100000000000000 : ℝ)^51
        have hw : |(-7743156337/10000000000 : ℝ)|=(7743156337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(694241641/2500000000 : ℝ)|^67 ≤ (18578240485483/100000000000000 : ℝ)^51
        have hw : |(694241641/2500000000 : ℝ)|=(694241641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7355624077/10000000000 : ℝ)*x 0 + (2229749083/10000000000 : ℝ)*x 1 + (2855953127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7355624077/10000000000 : ℝ)^67 ≤ (66799724451023/100000000000000 : ℝ)^51 := by
    have hnat : (7355624077 : ℕ)^67*100000000000000^51 ≤ 66799724451023^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7355624077 10000000000 66799724451023 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2229749083/10000000000 : ℝ)^67 ≤ (13924746135611/100000000000000 : ℝ)^51 := by
    have hnat : (2229749083 : ℕ)^67*100000000000000^51 ≤ 13924746135611^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229749083 10000000000 13924746135611 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2855953127/10000000000 : ℝ)^67 ≤ (9637764698921/50000000000000 : ℝ)^51 := by
    have hnat : (2855953127 : ℕ)^67*50000000000000^51 ≤ 9637764698921^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855953127 10000000000 9637764698921 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7355624077/10000000000 : ℝ), (2229749083/10000000000 : ℝ), (2855953127/10000000000 : ℝ)] ![(66799724451023/100000000000000 : ℝ), (13924746135611/100000000000000 : ℝ), (9637764698921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7355624077/10000000000 : ℝ)|^67 ≤ (66799724451023/100000000000000 : ℝ)^51
        have hw : |(7355624077/10000000000 : ℝ)|=(7355624077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2229749083/10000000000 : ℝ)|^67 ≤ (13924746135611/100000000000000 : ℝ)^51
        have hw : |(2229749083/10000000000 : ℝ)|=(2229749083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2855953127/10000000000 : ℝ)|^67 ≤ (9637764698921/50000000000000 : ℝ)^51
        have hw : |(2855953127/10000000000 : ℝ)|=(2855953127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1371049653/5000000000 : ℝ)*x 0 + (-3962900043/10000000000 : ℝ)*x 1 + (-608654201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1371049653/5000000000 : ℝ)^67 ≤ (18272398102603/100000000000000 : ℝ)^51 := by
    have hnat : (1371049653 : ℕ)^67*100000000000000^51 ≤ 18272398102603^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371049653 5000000000 18272398102603 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3962900043/10000000000 : ℝ)^67 ≤ (1185658387639/4000000000000 : ℝ)^51 := by
    have hnat : (3962900043 : ℕ)^67*4000000000000^51 ≤ 1185658387639^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3962900043 10000000000 1185658387639 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (608654201/1000000000 : ℝ)^67 ≤ (52086142191451/100000000000000 : ℝ)^51 := by
    have hnat : (608654201 : ℕ)^67*100000000000000^51 ≤ 52086142191451^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608654201 1000000000 52086142191451 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1371049653/5000000000 : ℝ), (-3962900043/10000000000 : ℝ), (-608654201/1000000000 : ℝ)] ![(18272398102603/100000000000000 : ℝ), (1185658387639/4000000000000 : ℝ), (52086142191451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1371049653/5000000000 : ℝ)|^67 ≤ (18272398102603/100000000000000 : ℝ)^51
        have hw : |(1371049653/5000000000 : ℝ)|=(1371049653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3962900043/10000000000 : ℝ)|^67 ≤ (1185658387639/4000000000000 : ℝ)^51
        have hw : |(-3962900043/10000000000 : ℝ)|=(3962900043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-608654201/1000000000 : ℝ)|^67 ≤ (52086142191451/100000000000000 : ℝ)^51
        have hw : |(-608654201/1000000000 : ℝ)|=(608654201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302013_s1_s1_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2761663027/10000000000 : ℝ)*x 0 + (-257532937/1250000000 : ℝ)*x 1 + (301589979/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2761663027/10000000000 : ℝ)^67 ≤ (18443854397983/100000000000000 : ℝ)^51 := by
    have hnat : (2761663027 : ℕ)^67*100000000000000^51 ≤ 18443854397983^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761663027 10000000000 18443854397983 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257532937/1250000000 : ℝ)^67 ≤ (12551130689169/100000000000000 : ℝ)^51 := by
    have hnat : (257532937 : ℕ)^67*100000000000000^51 ≤ 12551130689169^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257532937 1250000000 12551130689169 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (301589979/400000000 : ℝ)^67 ≤ (13801002979357/20000000000000 : ℝ)^51 := by
    have hnat : (301589979 : ℕ)^67*20000000000000^51 ≤ 13801002979357^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301589979 400000000 13801002979357 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2761663027/10000000000 : ℝ), (-257532937/1250000000 : ℝ), (301589979/400000000 : ℝ)] ![(18443854397983/100000000000000 : ℝ), (12551130689169/100000000000000 : ℝ), (13801002979357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2761663027/10000000000 : ℝ)|^67 ≤ (18443854397983/100000000000000 : ℝ)^51
        have hw : |(2761663027/10000000000 : ℝ)|=(2761663027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257532937/1250000000 : ℝ)|^67 ≤ (12551130689169/100000000000000 : ℝ)^51
        have hw : |(-257532937/1250000000 : ℝ)|=(257532937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(301589979/400000000 : ℝ)|^67 ≤ (13801002979357/20000000000000 : ℝ)^51
        have hw : |(301589979/400000000 : ℝ)|=(301589979/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302013_s1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((75911/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75911/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-37133/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-37133/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66717/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(66717/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1469/5000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-1469/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27069/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27069/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (75911/100000 : ℝ) ^ (65/16 : ℝ) ≤ (8159769737454979647/25000000000000000000 : ℝ) := by
    have hpowers : (75911/100000 : ℝ)^65 ≤ (8159769737454979647/25000000000000000000 : ℝ)^16 := by
      have hnat : (75911 : ℕ)^65*25000000000000000000^16 ≤ 8159769737454979647^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75911 100000 8159769737454979647 25000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75911/100000 : ℝ)) (X := (8159769737454979647/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (33159769737454979647/25000000000000000000 : ℝ) ≤ (536001574276167/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (33159769737454979647/25000000000000000000 : ℝ)^16 ≤ (536001574276167/500000000000000 : ℝ)^65 := by
      have hnat : (33159769737454979647 : ℕ)^16*500000000000000^65 ≤ 536001574276167^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33159769737454979647 25000000000000000000 536001574276167 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (536001574276167/500000000000000 : ℝ)) (X := (33159769737454979647/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (20659769737454979647/12500000000000000000 : ℝ) ≤ (5658281893360343/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (20659769737454979647/12500000000000000000 : ℝ)^16 ≤ (5658281893360343/5000000000000000 : ℝ)^65 := by
      have hnat : (20659769737454979647 : ℕ)^16*5000000000000000^65 ≤ 5658281893360343^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20659769737454979647 12500000000000000000 5658281893360343 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5658281893360343/5000000000000000 : ℝ)) (X := (20659769737454979647/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(36001574276167/379555000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(298266150598673/3795550000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (75911/100000 : ℝ)) (alpha := (36001574276167/379555000000000 : ℝ)) (beta := (298266150598673/3795550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (75911/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(36001574276167/379555000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(298266150598673/3795550000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (37133/50000 : ℝ) ^ (65/16 : ℝ) ≤ (7464909014927562987/25000000000000000000 : ℝ) := by
    have hpowers : (37133/50000 : ℝ)^65 ≤ (7464909014927562987/25000000000000000000 : ℝ)^16 := by
      have hnat : (37133 : ℕ)^65*25000000000000000000^16 ≤ 7464909014927562987^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37133 50000 7464909014927562987 25000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37133/50000 : ℝ)) (X := (7464909014927562987/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (32464909014927562987/25000000000000000000 : ℝ) ≤ (10664293919331603/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (32464909014927562987/25000000000000000000 : ℝ)^16 ≤ (10664293919331603/10000000000000000 : ℝ)^65 := by
      have hnat : (32464909014927562987 : ℕ)^16*10000000000000000^65 ≤ 10664293919331603^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32464909014927562987 25000000000000000000 10664293919331603 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10664293919331603/10000000000000000 : ℝ)) (X := (32464909014927562987/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (19964909014927562987/12500000000000000000 : ℝ) ≤ (1122166209197453/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (19964909014927562987/12500000000000000000 : ℝ)^16 ≤ (1122166209197453/1000000000000000 : ℝ)^65 := by
      have hnat : (19964909014927562987 : ℕ)^16*1000000000000000^65 ≤ 1122166209197453^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19964909014927562987 12500000000000000000 1122166209197453 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1122166209197453/1000000000000000 : ℝ)) (X := (19964909014927562987/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(664293919331603/7426600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(557368172642927/7426600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (37133/50000 : ℝ)) (alpha := (664293919331603/7426600000000000 : ℝ)) (beta := (557368172642927/7426600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (37133/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(664293919331603/7426600000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(557368172642927/7426600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (66717/100000 : ℝ) ^ (65/16 : ℝ) ≤ (3863588064433667829/20000000000000000000 : ℝ) := by
    have hpowers : (66717/100000 : ℝ)^65 ≤ (3863588064433667829/20000000000000000000 : ℝ)^16 := by
      have hnat : (66717 : ℕ)^65*20000000000000000000^16 ≤ 3863588064433667829^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66717 100000 3863588064433667829 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66717/100000 : ℝ)) (X := (3863588064433667829/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (23863588064433667829/20000000000000000000 : ℝ) ≤ (5222174974283019/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (23863588064433667829/20000000000000000000 : ℝ)^16 ≤ (5222174974283019/5000000000000000 : ℝ)^65 := by
      have hnat : (23863588064433667829 : ℕ)^16*5000000000000000^65 ≤ 5222174974283019^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23863588064433667829 20000000000000000000 5222174974283019 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5222174974283019/5000000000000000 : ℝ)) (X := (23863588064433667829/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (13863588064433667829/10000000000000000000 : ℝ) ≤ (677334587681343/625000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (13863588064433667829/10000000000000000000 : ℝ)^16 ≤ (677334587681343/625000000000000 : ℝ)^65 := by
      have hnat : (13863588064433667829 : ℕ)^16*625000000000000^65 ≤ 677334587681343^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13863588064433667829 10000000000000000000 677334587681343 625000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (677334587681343/625000000000000 : ℝ)) (X := (13863588064433667829/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(222174974283019/3335850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(374289004129/6354000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (66717/100000 : ℝ)) (alpha := (222174974283019/3335850000000000 : ℝ)) (beta := (374289004129/6354000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (66717/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(222174974283019/3335850000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(374289004129/6354000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((1620510681/2500000000 : ℝ)*X 1 0+(146669229/500000000 : ℝ)*X 1 1+(3316402329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((811108727/2000000000 : ℝ)*X 2 0+(-408539523/1000000000 : ℝ)*X 2 1+(-4844632399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1472868733/5000000000 : ℝ)*X 0 0+(-2772252107/10000000000 : ℝ)*X 0 1+(6897451159/10000000000 : ℝ)*X 0 2+(1472868733/5000000000 : ℝ)*X 1 0+(-2772252107/10000000000 : ℝ)*X 1 1+(6897451159/10000000000 : ℝ)*X 1 2+(1472868733/5000000000 : ℝ)*X 2 0+(-2772252107/10000000000 : ℝ)*X 2 1+(6897451159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2343903409/10000000000 : ℝ)*X 0 0+(-3746331129/5000000000 : ℝ)*X 0 1+(2559617851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((6435947391/10000000000 : ℝ)*X 1 0+(756197173/2500000000 : ℝ)*X 1 1+(3284793467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4118530987/10000000000 : ℝ)*X 2 0+(-4053107893/10000000000 : ℝ)*X 2 1+(-1203864487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((407909137/2000000000 : ℝ)*X 0 0+(-934754843/10000000000 : ℝ)*X 0 1+(4345608263/5000000000 : ℝ)*X 0 2+(407909137/2000000000 : ℝ)*X 1 0+(-934754843/10000000000 : ℝ)*X 1 1+(4345608263/5000000000 : ℝ)*X 1 2+(407909137/2000000000 : ℝ)*X 2 0+(-934754843/10000000000 : ℝ)*X 2 1+(4345608263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-2970952497/10000000000 : ℝ)*X 0 0+(-6463941727/10000000000 : ℝ)*X 0 1+(3302498259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7516759089/10000000000 : ℝ)*X 1 0+(1183715787/5000000000 : ℝ)*X 1 1+(2502726223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3861894149/10000000000 : ℝ)*X 2 0+(-432464327/1000000000 : ℝ)*X 2 1+(-4797471009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((686496143/5000000000 : ℝ)*X 0 0+(-366856557/2500000000 : ℝ)*X 0 1+(8804614371/10000000000 : ℝ)*X 0 2+(686496143/5000000000 : ℝ)*X 1 0+(-366856557/2500000000 : ℝ)*X 1 1+(8804614371/10000000000 : ℝ)*X 1 2+(686496143/5000000000 : ℝ)*X 2 0+(-366856557/2500000000 : ℝ)*X 2 1+(8804614371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-345571463/2000000000 : ℝ)*X 0 0+(-7743156337/10000000000 : ℝ)*X 0 1+(694241641/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7355624077/10000000000 : ℝ)*X 1 0+(2229749083/10000000000 : ℝ)*X 1 1+(2855953127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1371049653/5000000000 : ℝ)*X 2 0+(-3962900043/10000000000 : ℝ)*X 2 1+(-608654201/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2761663027/10000000000 : ℝ)*X 0 0+(-257532937/1250000000 : ℝ)*X 0 1+(301589979/400000000 : ℝ)*X 0 2+(2761663027/10000000000 : ℝ)*X 1 0+(-257532937/1250000000 : ℝ)*X 1 1+(301589979/400000000 : ℝ)*X 1 2+(2761663027/10000000000 : ℝ)*X 2 0+(-257532937/1250000000 : ℝ)*X 2 1+(301589979/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302013_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((30337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (355526050098274595889334443779/46781614583550000000000000000000000 : ℝ) := by norm_num
    linear_combination (1054203/1000000000000 : ℝ)*(base19) + (3027564841/12500000000 : ℝ)*(base40) + (281823/1000000000000 : ℝ)*(base49) + (622298695897/1000000000000 : ℝ)*(base50) + (1687691/1000000000000 : ℝ)*(base59) + (2045974619741/500000000000 : ℝ)*(major_s1_0) + (2045974619741/500000000000 : ℝ)*(major_s1_1) + (2045974619741/500000000000 : ℝ)*(major_s1_2) + (544069770227/100000000000 : ℝ)*(sp_s1_7) + (2720374998393/500000000000 : ℝ)*(sp_s1_8) + (5440751050989/1000000000000 : ℝ)*(sp_s1_9) + (274310115127/100000000000 : ℝ)*(sp_s1_13) + (43743469/1000000000000 : ℝ)*(sp_s1_20) + (53348719/1000000000000 : ℝ)*(sp_s1_21) + (2743144894739/1000000000000 : ℝ)*(f.failure) + (5440751050989/1000000000000 : ℝ)*(f.sum) + (33662158139198246153/247740236100000000000000000000000 : ℝ)*base62 + (850807959899/6354000000000000000000000 : ℝ)*base65 + (3610355023253743/3713300000000000000000000000 : ℝ)*base66 + (467079229947173/833962500000000000000000000 : ℝ)*base68 + (382082861134391/1124856562500000000000000000 : ℝ)*base70 + (7495005218307/56650000000000000000000000 : ℝ)*base72 + (1907650527446733/3713300000000000000000000000 : ℝ)*base74 + (4217906147791/11330000000000000000000000 : ℝ)*base77 + (2807680267985628771/4207168900000000000000000000000 : ℝ)*base78 + (1663/10000000000000000 : ℝ)*base87 + (1663/10000000000000000 : ℝ)*base89 + (1663/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1469/5000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-1469/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4750276807360278917849264640361/348263130788650000000000000000000000 : ℝ) := by norm_num
    linear_combination (3845323/1000000000000 : ℝ)*(base13) + (715551/500000000000 : ℝ)*(base39) + (14998355313/25000000000 : ℝ)*(base40) + (35247252437/200000000000 : ℝ)*(base50) + (3838543607/40000000000 : ℝ)*(base60) + (3856237142481/1000000000000 : ℝ)*(major_s1_0) + (3856237142481/1000000000000 : ℝ)*(major_s1_1) + (3856237142481/1000000000000 : ℝ)*(major_s1_2) + (400772837/1000000000000 : ℝ)*(sp_s1_2) + (5127336750083/1000000000000 : ℝ)*(sp_s1_14) + (2563670297703/500000000000 : ℝ)*(sp_s1_15) + (2563469143189/500000000000 : ℝ)*(sp_s1_16) + (20196321429/7812500000 : ℝ)*(sp_s1_20) + (24003/15625000000 : ℝ)*(sp_s1_23) + (20196321429/7812500000 : ℝ)*(f.failure) + (2563670297703/500000000000 : ℝ)*(f.sum) + (6831098776137592967/55053385800000000000000000000000 : ℝ)*base62 + (175412482311/220625000000000000000000 : ℝ)*base65 + (4562658772016453/7426600000000000000000000000 : ℝ)*base66 + (189967842244219/370650000000000000000000000 : ℝ)*base68 + (72291395532765543/267965830000000000000000000000 : ℝ)*base71 + (5089953411321237/3795550000000000000000000000 : ℝ)*base72 + (7602616495573703/7426600000000000000000000000 : ℝ)*base74 + (209911656022459/189777500000000000000000000 : ℝ)*base77 + (354237688243603307047/563760632600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (519/625000000000000 : ℝ)*base87 + (519/625000000000000 : ℝ)*base89 + (519/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27069/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27069/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (175820753445825378022505215841/12437968956737500000000000000000000 : ℝ) := by norm_num
    linear_combination (194611895533/125000000000 : ℝ)*(base3) + (102894007227/100000000000 : ℝ)*(base40) + (747067533381/500000000000 : ℝ)*(base50) + (737332568277/250000000000 : ℝ)*(major_s1_0) + (737332568277/250000000000 : ℝ)*(major_s1_1) + (737332568277/250000000000 : ℝ)*(major_s1_2) + (9771849/1000000000000 : ℝ)*(sp_s1_1) + (38727587/1000000000000 : ℝ)*(sp_s1_6) + (6689649/100000000000 : ℝ)*(sp_s1_15) + (484823/7812500000 : ℝ)*(sp_s1_16) + (3921495364271/1000000000000 : ℝ)*(sp_s1_21) + (1369578465049/250000000000 : ℝ)*(sp_s1_22) + (3921433306927/1000000000000 : ℝ)*(sp_s1_23) + (84045315631/200000000000 : ℝ)*(sp_s1_27) + (988580235003/500000000000 : ℝ)*(f.failure) + (3921495364271/1000000000000 : ℝ)*(f.sum) + (9800940033264610907/41290039350000000000000000000000 : ℝ)*base62 + (439290575569/2647500000000000000000000 : ℝ)*base64 + (45923164683449/1856650000000000000000000000 : ℝ)*base67 + (69563825457209/1111950000000000000000000000 : ℝ)*base69 + (343675314108523163/803897490000000000000000000000 : ℝ)*base70 + (2339665140261929/3795550000000000000000000000 : ℝ)*base73 + (26773446935489/464162500000000000000000000 : ℝ)*base74 + (203656700033099/379555000000000000000000000 : ℝ)*base76 + (40998407312362792161/140940158150000000000000000000000 : ℝ)*base79 + (249/5000000000000000 : ℝ)*base86 + (249/5000000000000000 : ℝ)*base88 + (249/5000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((75911/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75911/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-37133/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-37133/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66717/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(66717/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1469/5000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-1469/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27069/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27069/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302013_s1 p hpa hpb X hX hprev0

#print axioms solution

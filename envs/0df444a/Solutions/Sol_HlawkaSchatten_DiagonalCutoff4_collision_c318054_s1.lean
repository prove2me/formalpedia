-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c318054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:23:24.113671+00:00
-- url     : https://prove2.me/submissions/f9f8cc79-0ea8-4254-a650-1c9d04670828

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
theorem collision_support_c318054_s1_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2633414671/5000000000 : ℝ)*x 0 + (2606477923/5000000000 : ℝ)*x 1 + (1728193783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633414671/5000000000 : ℝ)^79 ≤ (11188493228329/25000000000000 : ℝ)^63 := by
    have hnat : (2633414671 : ℕ)^79*25000000000000^63 ≤ 11188493228329^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633414671 5000000000 11188493228329 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606477923/5000000000 : ℝ)^79 ≤ (2761292371187/6250000000000 : ℝ)^63 := by
    have hnat : (2606477923 : ℕ)^79*6250000000000^63 ≤ 2761292371187^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606477923 5000000000 2761292371187 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1728193783/10000000000 : ℝ)^79 ≤ (11065349131853/100000000000000 : ℝ)^63 := by
    have hnat : (1728193783 : ℕ)^79*100000000000000^63 ≤ 11065349131853^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728193783 10000000000 11065349131853 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633414671/5000000000 : ℝ), (2606477923/5000000000 : ℝ), (1728193783/10000000000 : ℝ)] ![(11188493228329/25000000000000 : ℝ), (2761292371187/6250000000000 : ℝ), (11065349131853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633414671/5000000000 : ℝ)|^79 ≤ (11188493228329/25000000000000 : ℝ)^63
        have hw : |(2633414671/5000000000 : ℝ)|=(2633414671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606477923/5000000000 : ℝ)|^79 ≤ (2761292371187/6250000000000 : ℝ)^63
        have hw : |(2606477923/5000000000 : ℝ)|=(2606477923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1728193783/10000000000 : ℝ)|^79 ≤ (11065349131853/100000000000000 : ℝ)^63
        have hw : |(1728193783/10000000000 : ℝ)|=(1728193783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1322454761/2500000000 : ℝ)*x 0 + (655835059/1250000000 : ℝ)*x 1 + (-826282717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322454761/2500000000 : ℝ)^79 ≤ (44999072527579/100000000000000 : ℝ)^63 := by
    have hnat : (1322454761 : ℕ)^79*100000000000000^63 ≤ 44999072527579^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322454761 2500000000 44999072527579 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655835059/1250000000 : ℝ)^79 ≤ (44539383468829/100000000000000 : ℝ)^63 := by
    have hnat : (655835059 : ℕ)^79*100000000000000^63 ≤ 44539383468829^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655835059 1250000000 44539383468829 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826282717/5000000000 : ℝ)^79 ≤ (10461543993737/100000000000000 : ℝ)^63 := by
    have hnat : (826282717 : ℕ)^79*100000000000000^63 ≤ 10461543993737^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826282717 5000000000 10461543993737 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322454761/2500000000 : ℝ), (655835059/1250000000 : ℝ), (-826282717/5000000000 : ℝ)] ![(44999072527579/100000000000000 : ℝ), (44539383468829/100000000000000 : ℝ), (10461543993737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322454761/2500000000 : ℝ)|^79 ≤ (44999072527579/100000000000000 : ℝ)^63
        have hw : |(1322454761/2500000000 : ℝ)|=(1322454761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655835059/1250000000 : ℝ)|^79 ≤ (44539383468829/100000000000000 : ℝ)^63
        have hw : |(655835059/1250000000 : ℝ)|=(655835059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-826282717/5000000000 : ℝ)|^79 ≤ (10461543993737/100000000000000 : ℝ)^63
        have hw : |(-826282717/5000000000 : ℝ)|=(826282717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-126214837/2500000000 : ℝ)*x 0 + (4107318623/10000000000 : ℝ)*x 1 + (-7081245171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126214837/2500000000 : ℝ)^79 ≤ (2364922174409/100000000000000 : ℝ)^63 := by
    have hnat : (126214837 : ℕ)^79*100000000000000^63 ≤ 2364922174409^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126214837 2500000000 2364922174409 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4107318623/10000000000 : ℝ)^79 ≤ (16382663042137/50000000000000 : ℝ)^63 := by
    have hnat : (4107318623 : ℕ)^79*50000000000000^63 ≤ 16382663042137^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4107318623 10000000000 16382663042137 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7081245171/10000000000 : ℝ)^79 ≤ (64869751723289/100000000000000 : ℝ)^63 := by
    have hnat : (7081245171 : ℕ)^79*100000000000000^63 ≤ 64869751723289^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7081245171 10000000000 64869751723289 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126214837/2500000000 : ℝ), (4107318623/10000000000 : ℝ), (-7081245171/10000000000 : ℝ)] ![(2364922174409/100000000000000 : ℝ), (16382663042137/50000000000000 : ℝ), (64869751723289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126214837/2500000000 : ℝ)|^79 ≤ (2364922174409/100000000000000 : ℝ)^63
        have hw : |(-126214837/2500000000 : ℝ)|=(126214837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4107318623/10000000000 : ℝ)|^79 ≤ (16382663042137/50000000000000 : ℝ)^63
        have hw : |(4107318623/10000000000 : ℝ)|=(4107318623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7081245171/10000000000 : ℝ)|^79 ≤ (64869751723289/100000000000000 : ℝ)^63
        have hw : |(-7081245171/10000000000 : ℝ)|=(7081245171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2605506007/5000000000 : ℝ)*x 0 + (-405658217/5000000000 : ℝ)*x 1 + (-2947821009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2605506007/5000000000 : ℝ)^79 ≤ (44160020663949/100000000000000 : ℝ)^63 := by
    have hnat : (2605506007 : ℕ)^79*100000000000000^63 ≤ 44160020663949^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605506007 5000000000 44160020663949 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405658217/5000000000 : ℝ)^79 ≤ (2143528369299/50000000000000 : ℝ)^63 := by
    have hnat : (405658217 : ℕ)^79*50000000000000^63 ≤ 2143528369299^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405658217 5000000000 2143528369299 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2947821009/5000000000 : ℝ)^79 ≤ (51552922584731/100000000000000 : ℝ)^63 := by
    have hnat : (2947821009 : ℕ)^79*100000000000000^63 ≤ 51552922584731^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2947821009 5000000000 51552922584731 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2605506007/5000000000 : ℝ), (-405658217/5000000000 : ℝ), (-2947821009/5000000000 : ℝ)] ![(44160020663949/100000000000000 : ℝ), (2143528369299/50000000000000 : ℝ), (51552922584731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2605506007/5000000000 : ℝ)|^79 ≤ (44160020663949/100000000000000 : ℝ)^63
        have hw : |(2605506007/5000000000 : ℝ)|=(2605506007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405658217/5000000000 : ℝ)|^79 ≤ (2143528369299/50000000000000 : ℝ)^63
        have hw : |(-405658217/5000000000 : ℝ)|=(405658217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2947821009/5000000000 : ℝ)|^79 ≤ (51552922584731/100000000000000 : ℝ)^63
        have hw : |(-2947821009/5000000000 : ℝ)|=(2947821009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4735097939/10000000000 : ℝ)*x 0 + (6457430243/10000000000 : ℝ)*x 1 + (309327413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4735097939/10000000000 : ℝ)^79 ≤ (39162718473297/100000000000000 : ℝ)^63 := by
    have hnat : (4735097939 : ℕ)^79*100000000000000^63 ≤ 39162718473297^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4735097939 10000000000 39162718473297 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6457430243/10000000000 : ℝ)^79 ≤ (11557154486659/20000000000000 : ℝ)^63 := by
    have hnat : (6457430243 : ℕ)^79*20000000000000^63 ≤ 11557154486659^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6457430243 10000000000 11557154486659 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (309327413/5000000000 : ℝ)^79 ≤ (47679829393/1562500000000 : ℝ)^63 := by
    have hnat : (309327413 : ℕ)^79*1562500000000^63 ≤ 47679829393^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309327413 5000000000 47679829393 1562500000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4735097939/10000000000 : ℝ), (6457430243/10000000000 : ℝ), (309327413/5000000000 : ℝ)] ![(39162718473297/100000000000000 : ℝ), (11557154486659/20000000000000 : ℝ), (47679829393/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4735097939/10000000000 : ℝ)|^79 ≤ (39162718473297/100000000000000 : ℝ)^63
        have hw : |(4735097939/10000000000 : ℝ)|=(4735097939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6457430243/10000000000 : ℝ)|^79 ≤ (11557154486659/20000000000000 : ℝ)^63
        have hw : |(6457430243/10000000000 : ℝ)|=(6457430243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(309327413/5000000000 : ℝ)|^79 ≤ (47679829393/1562500000000 : ℝ)^63
        have hw : |(309327413/5000000000 : ℝ)|=(309327413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1232352507/2500000000 : ℝ)*x 0 + (158852861/250000000 : ℝ)*x 1 + (-118403033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1232352507/2500000000 : ℝ)^79 ≤ (20594185342221/50000000000000 : ℝ)^63 := by
    have hnat : (1232352507 : ℕ)^79*50000000000000^63 ≤ 20594185342221^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232352507 2500000000 20594185342221 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158852861/250000000 : ℝ)^79 ≤ (56628787490413/100000000000000 : ℝ)^63 := by
    have hnat : (158852861 : ℕ)^79*100000000000000^63 ≤ 56628787490413^63*250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158852861 250000000 56628787490413 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118403033/2500000000 : ℝ)^79 ≤ (1091420907721/50000000000000 : ℝ)^63 := by
    have hnat : (118403033 : ℕ)^79*50000000000000^63 ≤ 1091420907721^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118403033 2500000000 1091420907721 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1232352507/2500000000 : ℝ), (158852861/250000000 : ℝ), (-118403033/2500000000 : ℝ)] ![(20594185342221/50000000000000 : ℝ), (56628787490413/100000000000000 : ℝ), (1091420907721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1232352507/2500000000 : ℝ)|^79 ≤ (20594185342221/50000000000000 : ℝ)^63
        have hw : |(1232352507/2500000000 : ℝ)|=(1232352507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158852861/250000000 : ℝ)|^79 ≤ (56628787490413/100000000000000 : ℝ)^63
        have hw : |(158852861/250000000 : ℝ)|=(158852861/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118403033/2500000000 : ℝ)|^79 ≤ (1091420907721/50000000000000 : ℝ)^63
        have hw : |(-118403033/2500000000 : ℝ)|=(118403033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-7004251/2000000000 : ℝ)*x 0 + (4480591531/10000000000 : ℝ)*x 1 + (-3475419839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7004251/2000000000 : ℝ)^79 ≤ (41652389441/50000000000000 : ℝ)^63 := by
    have hnat : (7004251 : ℕ)^79*50000000000000^63 ≤ 41652389441^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7004251 2000000000 41652389441 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480591531/10000000000 : ℝ)^79 ≤ (18270717664167/50000000000000 : ℝ)^63 := by
    have hnat : (4480591531 : ℕ)^79*50000000000000^63 ≤ 18270717664167^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480591531 10000000000 18270717664167 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3475419839/5000000000 : ℝ)^79 ≤ (15843814969979/25000000000000 : ℝ)^63 := by
    have hnat : (3475419839 : ℕ)^79*25000000000000^63 ≤ 15843814969979^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3475419839 5000000000 15843814969979 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7004251/2000000000 : ℝ), (4480591531/10000000000 : ℝ), (-3475419839/5000000000 : ℝ)] ![(41652389441/50000000000000 : ℝ), (18270717664167/50000000000000 : ℝ), (15843814969979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7004251/2000000000 : ℝ)|^79 ≤ (41652389441/50000000000000 : ℝ)^63
        have hw : |(-7004251/2000000000 : ℝ)|=(7004251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480591531/10000000000 : ℝ)|^79 ≤ (18270717664167/50000000000000 : ℝ)^63
        have hw : |(4480591531/10000000000 : ℝ)|=(4480591531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3475419839/5000000000 : ℝ)|^79 ≤ (15843814969979/25000000000000 : ℝ)^63
        have hw : |(-3475419839/5000000000 : ℝ)|=(3475419839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4916005703/10000000000 : ℝ)*x 0 + (-1310140407/10000000000 : ℝ)*x 1 + (-5857327083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4916005703/10000000000 : ℝ)^79 ≤ (2565498289791/6250000000000 : ℝ)^63 := by
    have hnat : (4916005703 : ℕ)^79*6250000000000^63 ≤ 2565498289791^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4916005703 10000000000 2565498289791 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310140407/10000000000 : ℝ)^79 ≤ (7818880840989/100000000000000 : ℝ)^63 := by
    have hnat : (1310140407 : ℕ)^79*100000000000000^63 ≤ 7818880840989^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310140407 10000000000 7818880840989 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5857327083/10000000000 : ℝ)^79 ≤ (25566573251769/50000000000000 : ℝ)^63 := by
    have hnat : (5857327083 : ℕ)^79*50000000000000^63 ≤ 25566573251769^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5857327083 10000000000 25566573251769 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4916005703/10000000000 : ℝ), (-1310140407/10000000000 : ℝ), (-5857327083/10000000000 : ℝ)] ![(2565498289791/6250000000000 : ℝ), (7818880840989/100000000000000 : ℝ), (25566573251769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4916005703/10000000000 : ℝ)|^79 ≤ (2565498289791/6250000000000 : ℝ)^63
        have hw : |(4916005703/10000000000 : ℝ)|=(4916005703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1310140407/10000000000 : ℝ)|^79 ≤ (7818880840989/100000000000000 : ℝ)^63
        have hw : |(-1310140407/10000000000 : ℝ)|=(1310140407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5857327083/10000000000 : ℝ)|^79 ≤ (25566573251769/50000000000000 : ℝ)^63
        have hw : |(-5857327083/10000000000 : ℝ)|=(5857327083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1295957971/2000000000 : ℝ)*x 0 + (585975913/1250000000 : ℝ)*x 1 + (26278797/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295957971/2000000000 : ℝ)^79 ≤ (58036789214683/100000000000000 : ℝ)^63 := by
    have hnat : (1295957971 : ℕ)^79*100000000000000^63 ≤ 58036789214683^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295957971 2000000000 58036789214683 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (585975913/1250000000 : ℝ)^79 ≤ (38672879829059/100000000000000 : ℝ)^63 := by
    have hnat : (585975913 : ℕ)^79*100000000000000^63 ≤ 38672879829059^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585975913 1250000000 38672879829059 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26278797/400000000 : ℝ)^79 ≤ (3290330938603/100000000000000 : ℝ)^63 := by
    have hnat : (26278797 : ℕ)^79*100000000000000^63 ≤ 3290330938603^63*400000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26278797 400000000 3290330938603 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295957971/2000000000 : ℝ), (585975913/1250000000 : ℝ), (26278797/400000000 : ℝ)] ![(58036789214683/100000000000000 : ℝ), (38672879829059/100000000000000 : ℝ), (3290330938603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295957971/2000000000 : ℝ)|^79 ≤ (58036789214683/100000000000000 : ℝ)^63
        have hw : |(1295957971/2000000000 : ℝ)|=(1295957971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(585975913/1250000000 : ℝ)|^79 ≤ (38672879829059/100000000000000 : ℝ)^63
        have hw : |(585975913/1250000000 : ℝ)|=(585975913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26278797/400000000 : ℝ)|^79 ≤ (3290330938603/100000000000000 : ℝ)^63
        have hw : |(26278797/400000000 : ℝ)|=(26278797/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3104525467/5000000000 : ℝ)*x 0 + (4877844907/10000000000 : ℝ)*x 1 + (-819122559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3104525467/5000000000 : ℝ)^79 ≤ (55012350277721/100000000000000 : ℝ)^63 := by
    have hnat : (3104525467 : ℕ)^79*100000000000000^63 ≤ 55012350277721^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104525467 5000000000 55012350277721 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4877844907/10000000000 : ℝ)^79 ≤ (20324403031459/50000000000000 : ℝ)^63 := by
    have hnat : (4877844907 : ℕ)^79*50000000000000^63 ≤ 20324403031459^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4877844907 10000000000 20324403031459 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (819122559/10000000000 : ℝ)^79 ≤ (4338843652259/100000000000000 : ℝ)^63 := by
    have hnat : (819122559 : ℕ)^79*100000000000000^63 ≤ 4338843652259^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819122559 10000000000 4338843652259 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3104525467/5000000000 : ℝ), (4877844907/10000000000 : ℝ), (-819122559/10000000000 : ℝ)] ![(55012350277721/100000000000000 : ℝ), (20324403031459/50000000000000 : ℝ), (4338843652259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3104525467/5000000000 : ℝ)|^79 ≤ (55012350277721/100000000000000 : ℝ)^63
        have hw : |(3104525467/5000000000 : ℝ)|=(3104525467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4877844907/10000000000 : ℝ)|^79 ≤ (20324403031459/50000000000000 : ℝ)^63
        have hw : |(4877844907/10000000000 : ℝ)|=(4877844907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-819122559/10000000000 : ℝ)|^79 ≤ (4338843652259/100000000000000 : ℝ)^63
        have hw : |(-819122559/10000000000 : ℝ)|=(819122559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1252219/10000000000 : ℝ)*x 0 + (5308331391/10000000000 : ℝ)*x 1 + (-6190118349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1252219/10000000000 : ℝ)^79 ≤ (1278247541/100000000000000 : ℝ)^63 := by
    have hnat : (1252219 : ℕ)^79*100000000000000^63 ≤ 1278247541^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252219 10000000000 1278247541 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5308331391/10000000000 : ℝ)^79 ≤ (45196634593573/100000000000000 : ℝ)^63 := by
    have hnat : (5308331391 : ℕ)^79*100000000000000^63 ≤ 45196634593573^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5308331391 10000000000 45196634593573 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6190118349/10000000000 : ℝ)^79 ≤ (54802087152291/100000000000000 : ℝ)^63 := by
    have hnat : (6190118349 : ℕ)^79*100000000000000^63 ≤ 54802087152291^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6190118349 10000000000 54802087152291 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1252219/10000000000 : ℝ), (5308331391/10000000000 : ℝ), (-6190118349/10000000000 : ℝ)] ![(1278247541/100000000000000 : ℝ), (45196634593573/100000000000000 : ℝ), (54802087152291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1252219/10000000000 : ℝ)|^79 ≤ (1278247541/100000000000000 : ℝ)^63
        have hw : |(-1252219/10000000000 : ℝ)|=(1252219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5308331391/10000000000 : ℝ)|^79 ≤ (45196634593573/100000000000000 : ℝ)^63
        have hw : |(5308331391/10000000000 : ℝ)|=(5308331391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6190118349/10000000000 : ℝ)|^79 ≤ (54802087152291/100000000000000 : ℝ)^63
        have hw : |(-6190118349/10000000000 : ℝ)|=(6190118349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (51568243/80000000 : ℝ)*x 0 + (-75609829/625000000 : ℝ)*x 1 + (-217776449/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51568243/80000000 : ℝ)^79 ≤ (7207234804849/12500000000000 : ℝ)^63 := by
    have hnat : (51568243 : ℕ)^79*12500000000000^63 ≤ 7207234804849^63*80000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51568243 80000000 7207234804849 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75609829/625000000 : ℝ)^79 ≤ (1768775526187/25000000000000 : ℝ)^63 := by
    have hnat : (75609829 : ℕ)^79*25000000000000^63 ≤ 1768775526187^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75609829 625000000 1768775526187 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217776449/500000000 : ℝ)^79 ≤ (17633509722983/50000000000000 : ℝ)^63 := by
    have hnat : (217776449 : ℕ)^79*50000000000000^63 ≤ 17633509722983^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217776449 500000000 17633509722983 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51568243/80000000 : ℝ), (-75609829/625000000 : ℝ), (-217776449/500000000 : ℝ)] ![(7207234804849/12500000000000 : ℝ), (1768775526187/25000000000000 : ℝ), (17633509722983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51568243/80000000 : ℝ)|^79 ≤ (7207234804849/12500000000000 : ℝ)^63
        have hw : |(51568243/80000000 : ℝ)|=(51568243/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75609829/625000000 : ℝ)|^79 ≤ (1768775526187/25000000000000 : ℝ)^63
        have hw : |(-75609829/625000000 : ℝ)|=(75609829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217776449/500000000 : ℝ)|^79 ≤ (17633509722983/50000000000000 : ℝ)^63
        have hw : |(-217776449/500000000 : ℝ)|=(217776449/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (160247581/312500000 : ℝ)*x 0 + (5423334051/10000000000 : ℝ)*x 1 + (1631337151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (160247581/312500000 : ℝ)^79 ≤ (10819714685123/25000000000000 : ℝ)^63 := by
    have hnat : (160247581 : ℕ)^79*25000000000000^63 ≤ 10819714685123^63*312500000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160247581 312500000 10819714685123 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423334051/10000000000 : ℝ)^79 ≤ (11606959115853/25000000000000 : ℝ)^63 := by
    have hnat : (5423334051 : ℕ)^79*25000000000000^63 ≤ 11606959115853^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423334051 10000000000 11606959115853 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1631337151/10000000000 : ℝ)^79 ≤ (10293304770249/100000000000000 : ℝ)^63 := by
    have hnat : (1631337151 : ℕ)^79*100000000000000^63 ≤ 10293304770249^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1631337151 10000000000 10293304770249 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(160247581/312500000 : ℝ), (5423334051/10000000000 : ℝ), (1631337151/10000000000 : ℝ)] ![(10819714685123/25000000000000 : ℝ), (11606959115853/25000000000000 : ℝ), (10293304770249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(160247581/312500000 : ℝ)|^79 ≤ (10819714685123/25000000000000 : ℝ)^63
        have hw : |(160247581/312500000 : ℝ)|=(160247581/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423334051/10000000000 : ℝ)|^79 ≤ (11606959115853/25000000000000 : ℝ)^63
        have hw : |(5423334051/10000000000 : ℝ)|=(5423334051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1631337151/10000000000 : ℝ)|^79 ≤ (10293304770249/100000000000000 : ℝ)^63
        have hw : |(1631337151/10000000000 : ℝ)|=(1631337151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318054_s1_s1_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2913246871/5000000000 : ℝ)*x 0 + (1214050453/2500000000 : ℝ)*x 1 + (-1437225893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2913246871/5000000000 : ℝ)^79 ≤ (12698961034681/25000000000000 : ℝ)^63 := by
    have hnat : (2913246871 : ℕ)^79*25000000000000^63 ≤ 12698961034681^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2913246871 5000000000 12698961034681 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214050453/2500000000 : ℝ)^79 ≤ (808455369343/2000000000000 : ℝ)^63 := by
    have hnat : (1214050453 : ℕ)^79*2000000000000^63 ≤ 808455369343^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214050453 2500000000 808455369343 2000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1437225893/10000000000 : ℝ)^79 ≤ (4390693694781/50000000000000 : ℝ)^63 := by
    have hnat : (1437225893 : ℕ)^79*50000000000000^63 ≤ 4390693694781^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437225893 10000000000 4390693694781 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2913246871/5000000000 : ℝ), (1214050453/2500000000 : ℝ), (-1437225893/10000000000 : ℝ)] ![(12698961034681/25000000000000 : ℝ), (808455369343/2000000000000 : ℝ), (4390693694781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2913246871/5000000000 : ℝ)|^79 ≤ (12698961034681/25000000000000 : ℝ)^63
        have hw : |(2913246871/5000000000 : ℝ)|=(2913246871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1214050453/2500000000 : ℝ)|^79 ≤ (808455369343/2000000000000 : ℝ)^63
        have hw : |(1214050453/2500000000 : ℝ)|=(1214050453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1437225893/10000000000 : ℝ)|^79 ≤ (4390693694781/50000000000000 : ℝ)^63
        have hw : |(-1437225893/10000000000 : ℝ)|=(1437225893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318054_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((72101/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72101/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75811/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75811/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13353/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13353/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4573/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4573/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48613/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48613/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3569/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3569/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s1_pow0 : (72101/100000 : ℝ) ^ (39/8 : ℝ) ≤ (20298492235374938431/100000000000000000000 : ℝ) := by
    have hpowers : (72101/100000 : ℝ)^39 ≤ (20298492235374938431/100000000000000000000 : ℝ)^8 := by
      have hnat : (72101 : ℕ)^39*100000000000000000000^8 ≤ 20298492235374938431^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72101 100000 20298492235374938431 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72101/100000 : ℝ)) (X := (20298492235374938431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (120298492235374938431/100000000000000000000 : ℝ) ≤ (2077273224382459/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (120298492235374938431/100000000000000000000 : ℝ)^8 ≤ (2077273224382459/2000000000000000 : ℝ)^39 := by
      have hnat : (120298492235374938431 : ℕ)^8*2000000000000000^39 ≤ 2077273224382459^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120298492235374938431 100000000000000000000 2077273224382459 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2077273224382459/2000000000000000 : ℝ)) (X := (120298492235374938431/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (70298492235374938431/50000000000000000000 : ℝ) ≤ (10723932025687467/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (70298492235374938431/50000000000000000000 : ℝ)^8 ≤ (10723932025687467/10000000000000000 : ℝ)^39 := by
      have hnat : (70298492235374938431 : ℕ)^8*10000000000000000^39 ≤ 10723932025687467^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70298492235374938431 50000000000000000000 10723932025687467 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10723932025687467/10000000000000000 : ℝ)) (X := (70298492235374938431/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(77273224382459/1442020000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(84391475943793/1802525000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (72101/100000 : ℝ)) (alpha := (77273224382459/1442020000000000 : ℝ)) (beta := (84391475943793/1802525000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (72101/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(77273224382459/1442020000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(84391475943793/1802525000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (75811/100000 : ℝ) ^ (39/8 : ℝ) ≤ (25923557426390091159/100000000000000000000 : ℝ) := by
    have hpowers : (75811/100000 : ℝ)^39 ≤ (25923557426390091159/100000000000000000000 : ℝ)^8 := by
      have hnat : (75811 : ℕ)^39*100000000000000000000^8 ≤ 25923557426390091159^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75811 100000 25923557426390091159 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75811/100000 : ℝ)) (X := (25923557426390091159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (125923557426390091159/100000000000000000000 : ℝ) ≤ (10484187179211123/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (125923557426390091159/100000000000000000000 : ℝ)^8 ≤ (10484187179211123/10000000000000000 : ℝ)^39 := by
      have hnat : (125923557426390091159 : ℕ)^8*10000000000000000^39 ≤ 10484187179211123^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125923557426390091159 100000000000000000000 10484187179211123 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10484187179211123/10000000000000000 : ℝ)) (X := (125923557426390091159/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (75923557426390091159/50000000000000000000 : ℝ) ≤ (10894607759692851/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (75923557426390091159/50000000000000000000 : ℝ)^8 ≤ (10894607759692851/10000000000000000 : ℝ)^39 := by
      have hnat : (75923557426390091159 : ℕ)^8*10000000000000000^39 ≤ 10894607759692851^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75923557426390091159 50000000000000000000 10894607759692851 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10894607759692851/10000000000000000 : ℝ)) (X := (75923557426390091159/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(484187179211123/7581100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(6412821570027/118454687500000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (75811/100000 : ℝ)) (alpha := (484187179211123/7581100000000000 : ℝ)) (beta := (6412821570027/118454687500000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75811/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(484187179211123/7581100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(6412821570027/118454687500000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13353/20000 : ℝ) ^ (39/8 : ℝ) ≤ (6976629569973166253/50000000000000000000 : ℝ) := by
    have hpowers : (13353/20000 : ℝ)^39 ≤ (6976629569973166253/50000000000000000000 : ℝ)^8 := by
      have hnat : (13353 : ℕ)^39*50000000000000000000^8 ≤ 6976629569973166253^8*20000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13353 20000 6976629569973166253 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13353/20000 : ℝ)) (X := (6976629569973166253/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (56976629569973166253/50000000000000000000 : ℝ) ≤ (1283944554195509/1250000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (56976629569973166253/50000000000000000000 : ℝ)^8 ≤ (1283944554195509/1250000000000000 : ℝ)^39 := by
      have hnat : (56976629569973166253 : ℕ)^8*1250000000000000^39 ≤ 1283944554195509^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56976629569973166253 50000000000000000000 1283944554195509 1250000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1283944554195509/1250000000000000 : ℝ)) (X := (56976629569973166253/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (31976629569973166253/25000000000000000000 : ℝ) ≤ (5258921732726211/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (31976629569973166253/25000000000000000000 : ℝ)^8 ≤ (5258921732726211/5000000000000000 : ℝ)^39 := by
      have hnat : (31976629569973166253 : ℕ)^8*5000000000000000^39 ≤ 5258921732726211^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31976629569973166253 25000000000000000000 5258921732726211 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5258921732726211/5000000000000000 : ℝ)) (X := (31976629569973166253/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(11314851398503/278187500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(4925740637767/133530000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (13353/20000 : ℝ)) (alpha := (11314851398503/278187500000000 : ℝ)) (beta := (4925740637767/133530000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13353/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(11314851398503/278187500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(4925740637767/133530000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_2 : ((2633414671/5000000000 : ℝ)*X 2 0+(2606477923/5000000000 : ℝ)*X 2 1+(1728193783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1322454761/2500000000 : ℝ)*X 0 0+(655835059/1250000000 : ℝ)*X 0 1+(-826282717/5000000000 : ℝ)*X 0 2+(1322454761/2500000000 : ℝ)*X 1 0+(655835059/1250000000 : ℝ)*X 1 1+(-826282717/5000000000 : ℝ)*X 1 2+(1322454761/2500000000 : ℝ)*X 2 0+(655835059/1250000000 : ℝ)*X 2 1+(-826282717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-126214837/2500000000 : ℝ)*X 0 0+(4107318623/10000000000 : ℝ)*X 0 1+(-7081245171/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2605506007/5000000000 : ℝ)*X 1 0+(-405658217/5000000000 : ℝ)*X 1 1+(-2947821009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4735097939/10000000000 : ℝ)*X 2 0+(6457430243/10000000000 : ℝ)*X 2 1+(309327413/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1232352507/2500000000 : ℝ)*X 0 0+(158852861/250000000 : ℝ)*X 0 1+(-118403033/2500000000 : ℝ)*X 0 2+(1232352507/2500000000 : ℝ)*X 1 0+(158852861/250000000 : ℝ)*X 1 1+(-118403033/2500000000 : ℝ)*X 1 2+(1232352507/2500000000 : ℝ)*X 2 0+(158852861/250000000 : ℝ)*X 2 1+(-118403033/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-7004251/2000000000 : ℝ)*X 0 0+(4480591531/10000000000 : ℝ)*X 0 1+(-3475419839/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4916005703/10000000000 : ℝ)*X 1 0+(-1310140407/10000000000 : ℝ)*X 1 1+(-5857327083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1295957971/2000000000 : ℝ)*X 2 0+(585975913/1250000000 : ℝ)*X 2 1+(26278797/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3104525467/5000000000 : ℝ)*X 0 0+(4877844907/10000000000 : ℝ)*X 0 1+(-819122559/10000000000 : ℝ)*X 0 2+(3104525467/5000000000 : ℝ)*X 1 0+(4877844907/10000000000 : ℝ)*X 1 1+(-819122559/10000000000 : ℝ)*X 1 2+(3104525467/5000000000 : ℝ)*X 2 0+(4877844907/10000000000 : ℝ)*X 2 1+(-819122559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1252219/10000000000 : ℝ)*X 0 0+(5308331391/10000000000 : ℝ)*X 0 1+(-6190118349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((51568243/80000000 : ℝ)*X 1 0+(-75609829/625000000 : ℝ)*X 1 1+(-217776449/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((160247581/312500000 : ℝ)*X 2 0+(5423334051/10000000000 : ℝ)*X 2 1+(1631337151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2913246871/5000000000 : ℝ)*X 0 0+(1214050453/2500000000 : ℝ)*X 0 1+(-1437225893/10000000000 : ℝ)*X 0 2+(2913246871/5000000000 : ℝ)*X 1 0+(1214050453/2500000000 : ℝ)*X 1 1+(-1437225893/10000000000 : ℝ)*X 1 2+(2913246871/5000000000 : ℝ)*X 2 0+(1214050453/2500000000 : ℝ)*X 2 1+(-1437225893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((4573/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4573/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24643147905830355870562295555193/1520586481428812500000000000000000000 : ℝ) := by norm_num
    linear_combination (5400001/250000000000 : ℝ)*(base23) + (153273219777/500000000000 : ℝ)*(base39) + (397427328339/1000000000000 : ℝ)*(base60) + (4305962930109/1000000000000 : ℝ)*(major_s1_0) + (4305962930109/1000000000000 : ℝ)*(major_s1_1) + (4305962930109/1000000000000 : ℝ)*(major_s1_2) + (38422479/1000000000000 : ℝ)*(sp_s1_6) + (6252109275639/1000000000000 : ℝ)*(sp_s1_7) + (6252043673181/1000000000000 : ℝ)*(sp_s1_8) + (3126046330841/500000000000 : ℝ)*(sp_s1_9) + (471943314831/200000000000 : ℝ)*(sp_s1_13) + (56185821/1000000000000 : ℝ)*(sp_s1_14) + (60894139/500000000000 : ℝ)*(sp_s1_15) + (51199773/1000000000000 : ℝ)*(sp_s1_23) + (1179877498317/500000000000 : ℝ)*(f.failure) + (6252165461459/1000000000000 : ℝ)*(f.sum) + (78537233793314554911/168717380500000000000000000000000 : ℝ)*base63 + (1066172092333/8902000000000000000000000 : ℝ)*base65 + (333689251496739/3790550000000000000000000000 : ℝ)*base67 + (264893800781927/278187500000000000000000000 : ℝ)*base69 + (216055001818476607/6418431020000000000000000000000 : ℝ)*base71 + (106612829486967/450631250000000000000000000 : ℝ)*base72 + (4923371254705107/7581100000000000000000000000 : ℝ)*base75 + (1272175902447757/1442020000000000000000000000 : ℝ)*base77 + (80991347618776571543/273302445550000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (2217/2000000000000000 : ℝ)*base86 + (2217/2000000000000000 : ℝ)*base88 + (2217/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48613/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48613/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3352507359905303488344492425523/190073310178601562500000000000000000 : ℝ) := by norm_num
    linear_combination (934627/50000000000 : ℝ)*(base21) + (3326781887/12500000000 : ℝ)*(base39) + (30813453149/500000000000 : ℝ)*(base60) + (2301470374301/500000000000 : ℝ)*(major_s1_0) + (2301470374301/500000000000 : ℝ)*(major_s1_1) + (2301470374301/500000000000 : ℝ)*(major_s1_2) + (8548953/200000000000 : ℝ)*(sp_s1_2) + (26935517/250000000000 : ℝ)*(sp_s1_7) + (5817809/100000000000 : ℝ)*(sp_s1_8) + (1670815753223/250000000000 : ℝ)*(sp_s1_14) + (668331257687/100000000000 : ℝ)*(sp_s1_15) + (835413664707/125000000000 : ℝ)*(sp_s1_16) + (2522466346939/1000000000000 : ℝ)*(sp_s1_20) + (1540639/40000000000 : ℝ)*(sp_s1_27) + (1261252431457/500000000000 : ℝ)*(f.failure) + (6683370754961/1000000000000 : ℝ)*(f.sum) + (6680759823894727729/84358690250000000000000000000000 : ℝ)*base63 + (12864346099417/133530000000000000000000000 : ℝ)*base65 + (639962856563307/947637500000000000000000000 : ℝ)*base66 + (338496141510037/556375000000000000000000000 : ℝ)*base69 + (2096940144923535179/4813823265000000000000000000000 : ℝ)*base70 + (1563365740757599/1802525000000000000000000000 : ℝ)*base72 + (701910490813207/3790550000000000000000000000 : ℝ)*base74 + (1936575506829/22531562500000000000000000 : ℝ)*base76 + (77000549072165308381/273302445550000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (643/2000000000000000 : ℝ)*base87 + (643/2000000000000000 : ℝ)*base89 + (643/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3569/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3569/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40465934153848708891676128075197/3041172962857625000000000000000000000 : ℝ) := by norm_num
    linear_combination (2235413/500000000000 : ℝ)*(base11) + (7682831/1000000000000 : ℝ)*(base15) + (77091078657/100000000000 : ℝ)*(base39) + (1503107/1000000000000 : ℝ)*(base40) + (4660236265087/1000000000000 : ℝ)*(major_s1_0) + (4660236265087/1000000000000 : ℝ)*(major_s1_1) + (4660236265087/1000000000000 : ℝ)*(major_s1_2) + (3919561/100000000000 : ℝ)*(sp_s1_9) + (182593/31250000000 : ℝ)*(sp_s1_16) + (83228799/1000000000000 : ℝ)*(sp_s1_20) + (1691639914071/250000000000 : ℝ)*(sp_s1_21) + (169163911107/25000000000 : ℝ)*(sp_s1_22) + (270660763541/40000000000 : ℝ)*(sp_s1_23) + (638455184729/250000000000 : ℝ)*(sp_s1_27) + (510780793543/200000000000 : ℝ)*(f.failure) + (6766564127111/1000000000000 : ℝ)*(f.sum) + (43663762475899602977/168717380500000000000000000000000 : ℝ)*base62 + (3258454727249/16691250000000000000000000 : ℝ)*base65 + (391444444045807/3790550000000000000000000000 : ℝ)*base67 + (315698507708453/556375000000000000000000000 : ℝ)*base68 + (6033517380623524283/19255293060000000000000000000000 : ℝ)*base70 + (1035934205279627/3605050000000000000000000000 : ℝ)*base73 + (4101149937852179/7581100000000000000000000000 : ℝ)*base74 + (225620602728051/288404000000000000000000000 : ℝ)*base76 + (11459379918335421599/68325611387500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (757/800000000000000 : ℝ)*base87 + (757/800000000000000 : ℝ)*base89 + (757/800000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((72101/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72101/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75811/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75811/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13353/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13353/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4573/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4573/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48613/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48613/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3569/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3569/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c318054_s1 p hpa hpb X hX hprev0

#print axioms solution

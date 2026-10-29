-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307075_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:16:26.698345+00:00
-- url     : https://prove2.me/submissions/fd607766-2746-4097-8f5f-db598cd524a9

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
theorem collision_support_c307075_s2_s2_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-385152659/2500000000 : ℝ)*x 0 + (-5923078147/10000000000 : ℝ)*x 1 + (1262366263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385152659/2500000000 : ℝ)^17 ≤ (4332337156367/50000000000000 : ℝ)^13 := by
    have hnat : (385152659 : ℕ)^17*50000000000000^13 ≤ 4332337156367^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385152659 2500000000 4332337156367 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5923078147/10000000000 : ℝ)^17 ≤ (12603816602699/25000000000000 : ℝ)^13 := by
    have hnat : (5923078147 : ℕ)^17*25000000000000^13 ≤ 12603816602699^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5923078147 10000000000 12603816602699 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1262366263/2500000000 : ℝ)^17 ≤ (20460029632883/50000000000000 : ℝ)^13 := by
    have hnat : (1262366263 : ℕ)^17*50000000000000^13 ≤ 20460029632883^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262366263 2500000000 20460029632883 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-385152659/2500000000 : ℝ), (-5923078147/10000000000 : ℝ), (1262366263/2500000000 : ℝ)] ![(4332337156367/50000000000000 : ℝ), (12603816602699/25000000000000 : ℝ), (20460029632883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-385152659/2500000000 : ℝ)|^17 ≤ (4332337156367/50000000000000 : ℝ)^13
        have hw : |(-385152659/2500000000 : ℝ)|=(385152659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5923078147/10000000000 : ℝ)|^17 ≤ (12603816602699/25000000000000 : ℝ)^13
        have hw : |(-5923078147/10000000000 : ℝ)|=(5923078147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1262366263/2500000000 : ℝ)|^17 ≤ (20460029632883/50000000000000 : ℝ)^13
        have hw : |(1262366263/2500000000 : ℝ)|=(1262366263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5159242837/10000000000 : ℝ)*x 0 + (-205471253/500000000 : ℝ)*x 1 + (-727664273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5159242837/10000000000 : ℝ)^17 ≤ (42087282368369/100000000000000 : ℝ)^13 := by
    have hnat : (5159242837 : ℕ)^17*100000000000000^13 ≤ 42087282368369^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159242837 10000000000 42087282368369 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205471253/500000000 : ℝ)^17 ≤ (31256796814859/100000000000000 : ℝ)^13 := by
    have hnat : (205471253 : ℕ)^17*100000000000000^13 ≤ 31256796814859^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205471253 500000000 31256796814859 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (727664273/2000000000 : ℝ)^17 ≤ (1066236832457/4000000000000 : ℝ)^13 := by
    have hnat : (727664273 : ℕ)^17*4000000000000^13 ≤ 1066236832457^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727664273 2000000000 1066236832457 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5159242837/10000000000 : ℝ), (-205471253/500000000 : ℝ), (-727664273/2000000000 : ℝ)] ![(42087282368369/100000000000000 : ℝ), (31256796814859/100000000000000 : ℝ), (1066236832457/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5159242837/10000000000 : ℝ)|^17 ≤ (42087282368369/100000000000000 : ℝ)^13
        have hw : |(5159242837/10000000000 : ℝ)|=(5159242837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205471253/500000000 : ℝ)|^17 ≤ (31256796814859/100000000000000 : ℝ)^13
        have hw : |(-205471253/500000000 : ℝ)|=(205471253/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-727664273/2000000000 : ℝ)|^17 ≤ (1066236832457/4000000000000 : ℝ)^13
        have hw : |(-727664273/2000000000 : ℝ)|=(727664273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (852037349/2500000000 : ℝ)*x 0 + (-2898780681/10000000000 : ℝ)*x 1 + (6394355209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852037349/2500000000 : ℝ)^17 ≤ (12236246144249/50000000000000 : ℝ)^13 := by
    have hnat : (852037349 : ℕ)^17*50000000000000^13 ≤ 12236246144249^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852037349 2500000000 12236246144249 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2898780681/10000000000 : ℝ)^17 ≤ (3960711018029/20000000000000 : ℝ)^13 := by
    have hnat : (2898780681 : ℕ)^17*20000000000000^13 ≤ 3960711018029^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2898780681 10000000000 3960711018029 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6394355209/10000000000 : ℝ)^17 ≤ (27861976297749/50000000000000 : ℝ)^13 := by
    have hnat : (6394355209 : ℕ)^17*50000000000000^13 ≤ 27861976297749^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6394355209 10000000000 27861976297749 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852037349/2500000000 : ℝ), (-2898780681/10000000000 : ℝ), (6394355209/10000000000 : ℝ)] ![(12236246144249/50000000000000 : ℝ), (3960711018029/20000000000000 : ℝ), (27861976297749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852037349/2500000000 : ℝ)|^17 ≤ (12236246144249/50000000000000 : ℝ)^13
        have hw : |(852037349/2500000000 : ℝ)|=(852037349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2898780681/10000000000 : ℝ)|^17 ≤ (3960711018029/20000000000000 : ℝ)^13
        have hw : |(-2898780681/10000000000 : ℝ)|=(2898780681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6394355209/10000000000 : ℝ)|^17 ≤ (27861976297749/50000000000000 : ℝ)^13
        have hw : |(6394355209/10000000000 : ℝ)|=(6394355209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-55939411/400000000 : ℝ)*x 0 + (-3247988313/5000000000 : ℝ)*x 1 + (4527677367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55939411/400000000 : ℝ)^17 ≤ (3817274659671/50000000000000 : ℝ)^13 := by
    have hnat : (55939411 : ℕ)^17*50000000000000^13 ≤ 3817274659671^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55939411 400000000 3817274659671 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3247988313/5000000000 : ℝ)^17 ≤ (56884846839143/100000000000000 : ℝ)^13 := by
    have hnat : (3247988313 : ℕ)^17*100000000000000^13 ≤ 56884846839143^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3247988313 5000000000 56884846839143 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527677367/10000000000 : ℝ)^17 ≤ (35480603829869/100000000000000 : ℝ)^13 := by
    have hnat : (4527677367 : ℕ)^17*100000000000000^13 ≤ 35480603829869^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527677367 10000000000 35480603829869 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55939411/400000000 : ℝ), (-3247988313/5000000000 : ℝ), (4527677367/10000000000 : ℝ)] ![(3817274659671/50000000000000 : ℝ), (56884846839143/100000000000000 : ℝ), (35480603829869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55939411/400000000 : ℝ)|^17 ≤ (3817274659671/50000000000000 : ℝ)^13
        have hw : |(-55939411/400000000 : ℝ)|=(55939411/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3247988313/5000000000 : ℝ)|^17 ≤ (56884846839143/100000000000000 : ℝ)^13
        have hw : |(-3247988313/5000000000 : ℝ)|=(3247988313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527677367/10000000000 : ℝ)|^17 ≤ (35480603829869/100000000000000 : ℝ)^13
        have hw : |(4527677367/10000000000 : ℝ)|=(4527677367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6379712147/10000000000 : ℝ)*x 0 + (1634127183/5000000000 : ℝ)*x 1 + (3062156327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6379712147/10000000000 : ℝ)^17 ≤ (3472321233827/6250000000000 : ℝ)^13 := by
    have hnat : (6379712147 : ℕ)^17*6250000000000^13 ≤ 3472321233827^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6379712147 10000000000 3472321233827 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1634127183/5000000000 : ℝ)^17 ≤ (23167254688729/100000000000000 : ℝ)^13 := by
    have hnat : (1634127183 : ℕ)^17*100000000000000^13 ≤ 23167254688729^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634127183 5000000000 23167254688729 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3062156327/10000000000 : ℝ)^17 ≤ (4255121110771/20000000000000 : ℝ)^13 := by
    have hnat : (3062156327 : ℕ)^17*20000000000000^13 ≤ 4255121110771^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3062156327 10000000000 4255121110771 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6379712147/10000000000 : ℝ), (1634127183/5000000000 : ℝ), (3062156327/10000000000 : ℝ)] ![(3472321233827/6250000000000 : ℝ), (23167254688729/100000000000000 : ℝ), (4255121110771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6379712147/10000000000 : ℝ)|^17 ≤ (3472321233827/6250000000000 : ℝ)^13
        have hw : |(6379712147/10000000000 : ℝ)|=(6379712147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1634127183/5000000000 : ℝ)|^17 ≤ (23167254688729/100000000000000 : ℝ)^13
        have hw : |(1634127183/5000000000 : ℝ)|=(1634127183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3062156327/10000000000 : ℝ)|^17 ≤ (4255121110771/20000000000000 : ℝ)^13
        have hw : |(3062156327/10000000000 : ℝ)|=(3062156327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5352224749/10000000000 : ℝ)*x 0 + (-3948950069/10000000000 : ℝ)*x 1 + (-896925321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352224749/10000000000 : ℝ)^17 ≤ (22078850126013/50000000000000 : ℝ)^13 := by
    have hnat : (5352224749 : ℕ)^17*50000000000000^13 ≤ 22078850126013^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352224749 10000000000 22078850126013 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3948950069/10000000000 : ℝ)^17 ≤ (3708789296269/12500000000000 : ℝ)^13 := by
    have hnat : (3948950069 : ℕ)^17*12500000000000^13 ≤ 3708789296269^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3948950069 10000000000 3708789296269 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896925321/2500000000 : ℝ)^17 ≤ (13085992679091/50000000000000 : ℝ)^13 := by
    have hnat : (896925321 : ℕ)^17*50000000000000^13 ≤ 13085992679091^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896925321 2500000000 13085992679091 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352224749/10000000000 : ℝ), (-3948950069/10000000000 : ℝ), (-896925321/2500000000 : ℝ)] ![(22078850126013/50000000000000 : ℝ), (3708789296269/12500000000000 : ℝ), (13085992679091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352224749/10000000000 : ℝ)|^17 ≤ (22078850126013/50000000000000 : ℝ)^13
        have hw : |(5352224749/10000000000 : ℝ)|=(5352224749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3948950069/10000000000 : ℝ)|^17 ≤ (3708789296269/12500000000000 : ℝ)^13
        have hw : |(-3948950069/10000000000 : ℝ)|=(3948950069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-896925321/2500000000 : ℝ)|^17 ≤ (13085992679091/50000000000000 : ℝ)^13
        have hw : |(-896925321/2500000000 : ℝ)|=(896925321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (662217709/2500000000 : ℝ)*x 0 + (-2169049747/10000000000 : ℝ)*x 1 + (7516623147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662217709/2500000000 : ℝ)^17 ≤ (3520229823713/20000000000000 : ℝ)^13 := by
    have hnat : (662217709 : ℕ)^17*20000000000000^13 ≤ 3520229823713^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662217709 2500000000 3520229823713 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169049747/10000000000 : ℝ)^17 ≤ (13553290507619/100000000000000 : ℝ)^13 := by
    have hnat : (2169049747 : ℕ)^17*100000000000000^13 ≤ 13553290507619^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169049747 10000000000 13553290507619 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7516623147/10000000000 : ℝ)^17 ≤ (13769112072623/20000000000000 : ℝ)^13 := by
    have hnat : (7516623147 : ℕ)^17*20000000000000^13 ≤ 13769112072623^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7516623147 10000000000 13769112072623 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662217709/2500000000 : ℝ), (-2169049747/10000000000 : ℝ), (7516623147/10000000000 : ℝ)] ![(3520229823713/20000000000000 : ℝ), (13553290507619/100000000000000 : ℝ), (13769112072623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662217709/2500000000 : ℝ)|^17 ≤ (3520229823713/20000000000000 : ℝ)^13
        have hw : |(662217709/2500000000 : ℝ)|=(662217709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2169049747/10000000000 : ℝ)|^17 ≤ (13553290507619/100000000000000 : ℝ)^13
        have hw : |(-2169049747/10000000000 : ℝ)|=(2169049747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7516623147/10000000000 : ℝ)|^17 ≤ (13769112072623/20000000000000 : ℝ)^13
        have hw : |(7516623147/10000000000 : ℝ)|=(7516623147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1124720803/10000000000 : ℝ)*x 0 + (-181757007/312500000 : ℝ)*x 1 + (5432782237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124720803/10000000000 : ℝ)^17 ≤ (2870968944897/50000000000000 : ℝ)^13 := by
    have hnat : (1124720803 : ℕ)^17*50000000000000^13 ≤ 2870968944897^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124720803 10000000000 2870968944897 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181757007/312500000 : ℝ)^17 ≤ (49229228570079/100000000000000 : ℝ)^13 := by
    have hnat : (181757007 : ℕ)^17*100000000000000^13 ≤ 49229228570079^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181757007 312500000 49229228570079 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432782237/10000000000 : ℝ)^17 ≤ (9005766705873/20000000000000 : ℝ)^13 := by
    have hnat : (5432782237 : ℕ)^17*20000000000000^13 ≤ 9005766705873^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432782237 10000000000 9005766705873 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1124720803/10000000000 : ℝ), (-181757007/312500000 : ℝ), (5432782237/10000000000 : ℝ)] ![(2870968944897/50000000000000 : ℝ), (49229228570079/100000000000000 : ℝ), (9005766705873/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1124720803/10000000000 : ℝ)|^17 ≤ (2870968944897/50000000000000 : ℝ)^13
        have hw : |(-1124720803/10000000000 : ℝ)|=(1124720803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-181757007/312500000 : ℝ)|^17 ≤ (49229228570079/100000000000000 : ℝ)^13
        have hw : |(-181757007/312500000 : ℝ)|=(181757007/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432782237/10000000000 : ℝ)|^17 ≤ (9005766705873/20000000000000 : ℝ)^13
        have hw : |(5432782237/10000000000 : ℝ)|=(5432782237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (683109763/1000000000 : ℝ)*x 0 + (3138724127/10000000000 : ℝ)*x 1 + (522216373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683109763/1000000000 : ℝ)^17 ≤ (60752546980511/100000000000000 : ℝ)^13 := by
    have hnat : (683109763 : ℕ)^17*100000000000000^13 ≤ 60752546980511^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683109763 1000000000 60752546980511 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3138724127/10000000000 : ℝ)^17 ≤ (21973941291523/100000000000000 : ℝ)^13 := by
    have hnat : (3138724127 : ℕ)^17*100000000000000^13 ≤ 21973941291523^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3138724127 10000000000 21973941291523 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522216373/2000000000 : ℝ)^17 ≤ (17273511709071/100000000000000 : ℝ)^13 := by
    have hnat : (522216373 : ℕ)^17*100000000000000^13 ≤ 17273511709071^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522216373 2000000000 17273511709071 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(683109763/1000000000 : ℝ), (3138724127/10000000000 : ℝ), (522216373/2000000000 : ℝ)] ![(60752546980511/100000000000000 : ℝ), (21973941291523/100000000000000 : ℝ), (17273511709071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(683109763/1000000000 : ℝ)|^17 ≤ (60752546980511/100000000000000 : ℝ)^13
        have hw : |(683109763/1000000000 : ℝ)|=(683109763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3138724127/10000000000 : ℝ)|^17 ≤ (21973941291523/100000000000000 : ℝ)^13
        have hw : |(3138724127/10000000000 : ℝ)|=(3138724127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522216373/2000000000 : ℝ)|^17 ≤ (17273511709071/100000000000000 : ℝ)^13
        have hw : |(522216373/2000000000 : ℝ)|=(522216373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5462933373/10000000000 : ℝ)*x 0 + (-4159623719/10000000000 : ℝ)*x 1 + (-3237984007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5462933373/10000000000 : ℝ)^17 ≤ (2834744305539/6250000000000 : ℝ)^13 := by
    have hnat : (5462933373 : ℕ)^17*6250000000000^13 ≤ 2834744305539^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462933373 10000000000 2834744305539 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4159623719/10000000000 : ℝ)^17 ≤ (31757031972071/100000000000000 : ℝ)^13 := by
    have hnat : (4159623719 : ℕ)^17*100000000000000^13 ≤ 31757031972071^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159623719 10000000000 31757031972071 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3237984007/10000000000 : ℝ)^17 ≤ (22887059121197/100000000000000 : ℝ)^13 := by
    have hnat : (3237984007 : ℕ)^17*100000000000000^13 ≤ 22887059121197^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3237984007 10000000000 22887059121197 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5462933373/10000000000 : ℝ), (-4159623719/10000000000 : ℝ), (-3237984007/10000000000 : ℝ)] ![(2834744305539/6250000000000 : ℝ), (31757031972071/100000000000000 : ℝ), (22887059121197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5462933373/10000000000 : ℝ)|^17 ≤ (2834744305539/6250000000000 : ℝ)^13
        have hw : |(5462933373/10000000000 : ℝ)|=(5462933373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4159623719/10000000000 : ℝ)|^17 ≤ (31757031972071/100000000000000 : ℝ)^13
        have hw : |(-4159623719/10000000000 : ℝ)|=(4159623719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3237984007/10000000000 : ℝ)|^17 ≤ (22887059121197/100000000000000 : ℝ)^13
        have hw : |(-3237984007/10000000000 : ℝ)|=(3237984007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1394995587/5000000000 : ℝ)*x 0 + (-584200843/2500000000 : ℝ)*x 1 + (1459326803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1394995587/5000000000 : ℝ)^17 ≤ (18837318662619/100000000000000 : ℝ)^13 := by
    have hnat : (1394995587 : ℕ)^17*100000000000000^13 ≤ 18837318662619^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394995587 5000000000 18837318662619 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (584200843/2500000000 : ℝ)^17 ≤ (466876582253/3125000000000 : ℝ)^13 := by
    have hnat : (584200843 : ℕ)^17*3125000000000^13 ≤ 466876582253^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584200843 2500000000 466876582253 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1459326803/2000000000 : ℝ)^17 ≤ (13244526138637/20000000000000 : ℝ)^13 := by
    have hnat : (1459326803 : ℕ)^17*20000000000000^13 ≤ 13244526138637^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459326803 2000000000 13244526138637 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1394995587/5000000000 : ℝ), (-584200843/2500000000 : ℝ), (1459326803/2000000000 : ℝ)] ![(18837318662619/100000000000000 : ℝ), (466876582253/3125000000000 : ℝ), (13244526138637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1394995587/5000000000 : ℝ)|^17 ≤ (18837318662619/100000000000000 : ℝ)^13
        have hw : |(1394995587/5000000000 : ℝ)|=(1394995587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-584200843/2500000000 : ℝ)|^17 ≤ (466876582253/3125000000000 : ℝ)^13
        have hw : |(-584200843/2500000000 : ℝ)|=(584200843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1459326803/2000000000 : ℝ)|^17 ≤ (13244526138637/20000000000000 : ℝ)^13
        have hw : |(1459326803/2000000000 : ℝ)|=(1459326803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-210296691/2000000000 : ℝ)*x 0 + (-1279664877/2000000000 : ℝ)*x 1 + (4864668951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210296691/2000000000 : ℝ)^17 ≤ (2628987882011/50000000000000 : ℝ)^13 := by
    have hnat : (210296691 : ℕ)^17*50000000000000^13 ≤ 2628987882011^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210296691 2000000000 2628987882011 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1279664877/2000000000 : ℝ)^17 ≤ (13942297366377/25000000000000 : ℝ)^13 := by
    have hnat : (1279664877 : ℕ)^17*25000000000000^13 ≤ 13942297366377^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279664877 2000000000 13942297366377 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4864668951/10000000000 : ℝ)^17 ≤ (19486417377961/50000000000000 : ℝ)^13 := by
    have hnat : (4864668951 : ℕ)^17*50000000000000^13 ≤ 19486417377961^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4864668951 10000000000 19486417377961 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210296691/2000000000 : ℝ), (-1279664877/2000000000 : ℝ), (4864668951/10000000000 : ℝ)] ![(2628987882011/50000000000000 : ℝ), (13942297366377/25000000000000 : ℝ), (19486417377961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210296691/2000000000 : ℝ)|^17 ≤ (2628987882011/50000000000000 : ℝ)^13
        have hw : |(-210296691/2000000000 : ℝ)|=(210296691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1279664877/2000000000 : ℝ)|^17 ≤ (13942297366377/25000000000000 : ℝ)^13
        have hw : |(-1279664877/2000000000 : ℝ)|=(1279664877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4864668951/10000000000 : ℝ)|^17 ≤ (19486417377961/50000000000000 : ℝ)^13
        have hw : |(4864668951/10000000000 : ℝ)|=(4864668951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (276173413/400000000 : ℝ)*x 0 + (588595991/2000000000 : ℝ)*x 1 + (2716940677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276173413/400000000 : ℝ)^17 ≤ (61605702521667/100000000000000 : ℝ)^13 := by
    have hnat : (276173413 : ℕ)^17*100000000000000^13 ≤ 61605702521667^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276173413 400000000 61605702521667 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (588595991/2000000000 : ℝ)^17 ≤ (20199342995151/100000000000000 : ℝ)^13 := by
    have hnat : (588595991 : ℕ)^17*100000000000000^13 ≤ 20199342995151^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588595991 2000000000 20199342995151 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716940677/10000000000 : ℝ)^17 ≤ (9097477234217/50000000000000 : ℝ)^13 := by
    have hnat : (2716940677 : ℕ)^17*50000000000000^13 ≤ 9097477234217^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716940677 10000000000 9097477234217 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(276173413/400000000 : ℝ), (588595991/2000000000 : ℝ), (2716940677/10000000000 : ℝ)] ![(61605702521667/100000000000000 : ℝ), (20199342995151/100000000000000 : ℝ), (9097477234217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(276173413/400000000 : ℝ)|^17 ≤ (61605702521667/100000000000000 : ℝ)^13
        have hw : |(276173413/400000000 : ℝ)|=(276173413/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(588595991/2000000000 : ℝ)|^17 ≤ (20199342995151/100000000000000 : ℝ)^13
        have hw : |(588595991/2000000000 : ℝ)|=(588595991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716940677/10000000000 : ℝ)|^17 ≤ (9097477234217/50000000000000 : ℝ)^13
        have hw : |(2716940677/10000000000 : ℝ)|=(2716940677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2524860973/5000000000 : ℝ)*x 0 + (-2070486967/5000000000 : ℝ)*x 1 + (-931686733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2524860973/5000000000 : ℝ)^17 ≤ (40922781677529/100000000000000 : ℝ)^13 := by
    have hnat : (2524860973 : ℕ)^17*100000000000000^13 ≤ 40922781677529^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524860973 5000000000 40922781677529 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070486967/5000000000 : ℝ)^17 ≤ (31570966718137/100000000000000 : ℝ)^13 := by
    have hnat : (2070486967 : ℕ)^17*100000000000000^13 ≤ 31570966718137^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070486967 5000000000 31570966718137 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931686733/2500000000 : ℝ)^17 ≤ (343828144949/1250000000000 : ℝ)^13 := by
    have hnat : (931686733 : ℕ)^17*1250000000000^13 ≤ 343828144949^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931686733 2500000000 343828144949 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2524860973/5000000000 : ℝ), (-2070486967/5000000000 : ℝ), (-931686733/2500000000 : ℝ)] ![(40922781677529/100000000000000 : ℝ), (31570966718137/100000000000000 : ℝ), (343828144949/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2524860973/5000000000 : ℝ)|^17 ≤ (40922781677529/100000000000000 : ℝ)^13
        have hw : |(2524860973/5000000000 : ℝ)|=(2524860973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2070486967/5000000000 : ℝ)|^17 ≤ (31570966718137/100000000000000 : ℝ)^13
        have hw : |(-2070486967/5000000000 : ℝ)|=(2070486967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-931686733/2500000000 : ℝ)|^17 ≤ (343828144949/1250000000000 : ℝ)^13
        have hw : |(-931686733/2500000000 : ℝ)|=(931686733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307075_s2_s2_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3661435689/10000000000 : ℝ)*x 0 + (-2656014883/10000000000 : ℝ)*x 1 + (3185553237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3661435689/10000000000 : ℝ)^17 ≤ (5375517766603/20000000000000 : ℝ)^13 := by
    have hnat : (3661435689 : ℕ)^17*20000000000000^13 ≤ 5375517766603^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661435689 10000000000 5375517766603 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2656014883/10000000000 : ℝ)^17 ≤ (110395323581/625000000000 : ℝ)^13 := by
    have hnat : (2656014883 : ℕ)^17*625000000000^13 ≤ 110395323581^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656014883 10000000000 110395323581 625000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185553237/5000000000 : ℝ)^17 ≤ (27729579689653/50000000000000 : ℝ)^13 := by
    have hnat : (3185553237 : ℕ)^17*50000000000000^13 ≤ 27729579689653^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185553237 5000000000 27729579689653 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3661435689/10000000000 : ℝ), (-2656014883/10000000000 : ℝ), (3185553237/5000000000 : ℝ)] ![(5375517766603/20000000000000 : ℝ), (110395323581/625000000000 : ℝ), (27729579689653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3661435689/10000000000 : ℝ)|^17 ≤ (5375517766603/20000000000000 : ℝ)^13
        have hw : |(3661435689/10000000000 : ℝ)|=(3661435689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2656014883/10000000000 : ℝ)|^17 ≤ (110395323581/625000000000 : ℝ)^13
        have hw : |(-2656014883/10000000000 : ℝ)|=(2656014883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185553237/5000000000 : ℝ)|^17 ≤ (27729579689653/50000000000000 : ℝ)^13
        have hw : |(3185553237/5000000000 : ℝ)|=(3185553237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307075_s2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((3581/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3581/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7893/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7893/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59121/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59121/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16073/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16073/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3241/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3241/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21469/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21469/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (3581/6250 : ℝ) ^ (135/32 : ℝ) ≤ (9540846443660788091/100000000000000000000 : ℝ) := by
    have hpowers : (3581/6250 : ℝ)^135 ≤ (9540846443660788091/100000000000000000000 : ℝ)^32 := by
      have hnat : (3581 : ℕ)^135*100000000000000000000^32 ≤ 9540846443660788091^32*6250^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3581 6250 9540846443660788091 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3581/6250 : ℝ)) (X := (9540846443660788091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (109540846443660788091/100000000000000000000 : ℝ) ≤ (2554588827007039/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (109540846443660788091/100000000000000000000 : ℝ)^32 ≤ (2554588827007039/2500000000000000 : ℝ)^135 := by
      have hnat : (109540846443660788091 : ℕ)^32*2500000000000000^135 ≤ 2554588827007039^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109540846443660788091 100000000000000000000 2554588827007039 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2554588827007039/2500000000000000 : ℝ)) (X := (109540846443660788091/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (59540846443660788091/50000000000000000000 : ℝ) ≤ (651415504985707/625000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (59540846443660788091/50000000000000000000 : ℝ)^32 ≤ (651415504985707/625000000000000 : ℝ)^135 := by
      have hnat : (59540846443660788091 : ℕ)^32*625000000000000^135 ≤ 651415504985707^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59540846443660788091 50000000000000000000 651415504985707 625000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (651415504985707/625000000000000 : ℝ)) (X := (59540846443660788091/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(54588827007039/1432400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(51073192935789/1432400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (3581/6250 : ℝ)) (alpha := (54588827007039/1432400000000000 : ℝ)) (beta := (51073192935789/1432400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3581/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(54588827007039/1432400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(51073192935789/1432400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (7893/10000 : ℝ) ^ (135/32 : ℝ) ≤ (9213616464058602909/25000000000000000000 : ℝ) := by
    have hpowers : (7893/10000 : ℝ)^135 ≤ (9213616464058602909/25000000000000000000 : ℝ)^32 := by
      have hnat : (7893 : ℕ)^135*25000000000000000000^32 ≤ 9213616464058602909^32*10000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7893 10000 9213616464058602909 25000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7893/10000 : ℝ)) (X := (9213616464058602909/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (34213616464058602909/25000000000000000000 : ℝ) ≤ (5386025779692221/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (34213616464058602909/25000000000000000000 : ℝ)^32 ≤ (5386025779692221/5000000000000000 : ℝ)^135 := by
      have hnat : (34213616464058602909 : ℕ)^32*5000000000000000^135 ≤ 5386025779692221^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34213616464058602909 25000000000000000000 5386025779692221 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5386025779692221/5000000000000000 : ℝ)) (X := (34213616464058602909/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (21713616464058602909/12500000000000000000 : ℝ) ≤ (11398474492931023/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (21713616464058602909/12500000000000000000 : ℝ)^32 ≤ (11398474492931023/10000000000000000 : ℝ)^135 := by
      have hnat : (21713616464058602909 : ℕ)^32*10000000000000000^135 ≤ 11398474492931023^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21713616464058602909 12500000000000000000 11398474492931023 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11398474492931023/10000000000000000 : ℝ)) (X := (21713616464058602909/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(128675259897407/1315500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(208807644515527/2631000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (7893/10000 : ℝ)) (alpha := (128675259897407/1315500000000000 : ℝ)) (beta := (208807644515527/2631000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (7893/10000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(128675259897407/1315500000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(208807644515527/2631000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (59121/100000 : ℝ) ^ (135/32 : ℝ) ≤ (10890193530385656371/100000000000000000000 : ℝ) := by
    have hpowers : (59121/100000 : ℝ)^135 ≤ (10890193530385656371/100000000000000000000 : ℝ)^32 := by
      have hnat : (59121 : ℕ)^135*100000000000000000000^32 ≤ 10890193530385656371^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59121 100000 10890193530385656371 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59121/100000 : ℝ)) (X := (10890193530385656371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (110890193530385656371/100000000000000000000 : ℝ) ≤ (5124026198397763/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (110890193530385656371/100000000000000000000 : ℝ)^32 ≤ (5124026198397763/5000000000000000 : ℝ)^135 := by
      have hnat : (110890193530385656371 : ℕ)^32*5000000000000000^135 ≤ 5124026198397763^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110890193530385656371 100000000000000000000 5124026198397763 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5124026198397763/5000000000000000 : ℝ)) (X := (110890193530385656371/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (60890193530385656371/50000000000000000000 : ℝ) ≤ (10478159414173653/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (60890193530385656371/50000000000000000000 : ℝ)^32 ≤ (10478159414173653/10000000000000000 : ℝ)^135 := by
      have hnat : (60890193530385656371 : ℕ)^32*10000000000000000^135 ≤ 10478159414173653^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60890193530385656371 50000000000000000000 10478159414173653 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10478159414173653/10000000000000000 : ℝ)) (X := (60890193530385656371/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(124026198397763/2956050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(230107017378127/5912100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (59121/100000 : ℝ)) (alpha := (124026198397763/2956050000000000 : ℝ)) (beta := (230107017378127/5912100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (59121/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(124026198397763/2956050000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(230107017378127/5912100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-385152659/2500000000 : ℝ)*X 0 0+(-5923078147/10000000000 : ℝ)*X 0 1+(1262366263/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5159242837/10000000000 : ℝ)*X 2 0+(-205471253/500000000 : ℝ)*X 2 1+(-727664273/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((852037349/2500000000 : ℝ)*X 0 0+(-2898780681/10000000000 : ℝ)*X 0 1+(6394355209/10000000000 : ℝ)*X 0 2+(852037349/2500000000 : ℝ)*X 1 0+(-2898780681/10000000000 : ℝ)*X 1 1+(6394355209/10000000000 : ℝ)*X 1 2+(852037349/2500000000 : ℝ)*X 2 0+(-2898780681/10000000000 : ℝ)*X 2 1+(6394355209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-55939411/400000000 : ℝ)*X 0 0+(-3247988313/5000000000 : ℝ)*X 0 1+(4527677367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((6379712147/10000000000 : ℝ)*X 1 0+(1634127183/5000000000 : ℝ)*X 1 1+(3062156327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((5352224749/10000000000 : ℝ)*X 2 0+(-3948950069/10000000000 : ℝ)*X 2 1+(-896925321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((662217709/2500000000 : ℝ)*X 0 0+(-2169049747/10000000000 : ℝ)*X 0 1+(7516623147/10000000000 : ℝ)*X 0 2+(662217709/2500000000 : ℝ)*X 1 0+(-2169049747/10000000000 : ℝ)*X 1 1+(7516623147/10000000000 : ℝ)*X 1 2+(662217709/2500000000 : ℝ)*X 2 0+(-2169049747/10000000000 : ℝ)*X 2 1+(7516623147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1124720803/10000000000 : ℝ)*X 0 0+(-181757007/312500000 : ℝ)*X 0 1+(5432782237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((683109763/1000000000 : ℝ)*X 1 0+(3138724127/10000000000 : ℝ)*X 1 1+(522216373/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5462933373/10000000000 : ℝ)*X 2 0+(-4159623719/10000000000 : ℝ)*X 2 1+(-3237984007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1394995587/5000000000 : ℝ)*X 0 0+(-584200843/2500000000 : ℝ)*X 0 1+(1459326803/2000000000 : ℝ)*X 0 2+(1394995587/5000000000 : ℝ)*X 1 0+(-584200843/2500000000 : ℝ)*X 1 1+(1459326803/2000000000 : ℝ)*X 1 2+(1394995587/5000000000 : ℝ)*X 2 0+(-584200843/2500000000 : ℝ)*X 2 1+(1459326803/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-210296691/2000000000 : ℝ)*X 0 0+(-1279664877/2000000000 : ℝ)*X 0 1+(4864668951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((276173413/400000000 : ℝ)*X 1 0+(588595991/2000000000 : ℝ)*X 1 1+(2716940677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2524860973/5000000000 : ℝ)*X 2 0+(-2070486967/5000000000 : ℝ)*X 2 1+(-931686733/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3661435689/10000000000 : ℝ)*X 0 0+(-2656014883/10000000000 : ℝ)*X 0 1+(3185553237/5000000000 : ℝ)*X 0 2+(3661435689/10000000000 : ℝ)*X 1 0+(-2656014883/10000000000 : ℝ)*X 1 1+(3185553237/5000000000 : ℝ)*X 1 2+(3661435689/10000000000 : ℝ)*X 2 0+(-2656014883/10000000000 : ℝ)*X 2 1+(3185553237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307075_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((16073/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16073/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2554181046893731455680812589/309452813295000000000000000000000 : ℝ) := by norm_num
    linear_combination (113942278411/125000000000 : ℝ)*(base40) + (520931/125000000000 : ℝ)*(base49) + (487273/1000000000000 : ℝ)*(base50) + (30144752881/250000000000 : ℝ)*(base60) + (66697045183/10000000000 : ℝ)*(major_s2_0) + (66697045183/10000000000 : ℝ)*(major_s2_1) + (66697045183/10000000000 : ℝ)*(major_s2_2) + (86229457/1000000000000 : ℝ)*(sp_s2_0) + (9048686198677/1000000000000 : ℝ)*(sp_s2_7) + (4524386214067/500000000000 : ℝ)*(sp_s2_8) + (9048488164943/1000000000000 : ℝ)*(sp_s2_9) + (1072610458983/250000000000 : ℝ)*(sp_s2_13) + (96010621/500000000000 : ℝ)*(sp_s2_20) + (284263191/1000000000000 : ℝ)*(sp_s2_23) + (2145316928587/500000000000 : ℝ)*(f.failure) + (4524386214067/500000000000 : ℝ)*(f.sum) + (131424053962448803/129622792500000000000000000000 : ℝ)*base63 + (524287316510879/591210000000000000000000000 : ℝ)*base65 + (439894432439/5262000000000000000000000 : ℝ)*base67 + (16871047732669/295605000000000000000000000 : ℝ)*base68 + (1012988940824547233/4234246020000000000000000000000 : ℝ)*base71 + (14556348681289/71620000000000000000000000 : ℝ)*base72 + (606445796729/6577500000000000000000000 : ℝ)*base75 + (27579411572303/71620000000000000000000000 : ℝ)*base77 + (123405334297267009/188432220000000000000000000000 : ℝ)*base79 + (1003/6250000000000000 : ℝ)*base86 + (1003/6250000000000000 : ℝ)*base88 + (1003/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-3241/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3241/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (96363544196737673132710726787/10315093776500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3996589/1000000000000 : ℝ)*(base39) + (1951488803519/1000000000000 : ℝ)*(base40) + (2591759/1000000000000 : ℝ)*(base49) + (73977434479/125000000000 : ℝ)*(base60) + (4602206278353/500000000000 : ℝ)*(major_s2_0) + (4602206278353/500000000000 : ℝ)*(major_s2_1) + (4602206278353/500000000000 : ℝ)*(major_s2_2) + (39999419/500000000000 : ℝ)*(sp_s2_0) + (160560609/1000000000000 : ℝ)*(sp_s2_13) + (3121881386113/250000000000 : ℝ)*(sp_s2_14) + (6243670099347/500000000000 : ℝ)*(sp_s2_15) + (1248760554329/100000000000 : ℝ)*(sp_s2_16) + (1480263973877/250000000000 : ℝ)*(sp_s2_20) + (66336149/250000000000 : ℝ)*(sp_s2_22) + (2960608228059/500000000000 : ℝ)*(f.failure) + (1248760554329/100000000000 : ℝ)*(f.sum) + (2761903381452490981/8641519500000000000000000000000 : ℝ)*base63 + (71680653635561/492675000000000000000000000 : ℝ)*base64 + (92352986167891/109625000000000000000000000 : ℝ)*base67 + (442340839382483/492675000000000000000000000 : ℝ)*base69 + (4713705173891970061/14114153400000000000000000000000 : ℝ)*base71 + (625648725674617/716200000000000000000000000 : ℝ)*base73 + (147973938723223/438500000000000000000000000 : ℝ)*base75 + (261752844700653/716200000000000000000000000 : ℝ)*base76 + (1804654613176784413/3140537000000000000000000000000 : ℝ)*base79 + (1929/6250000000000000 : ℝ)*base87 + (1929/6250000000000000 : ℝ)*base89 + (1929/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21469/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21469/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (51697289550572441524708183783/3094528132950000000000000000000000 : ℝ) := by norm_num
    linear_combination (879646623353/500000000000 : ℝ)*(base40) + (1968233/250000000000 : ℝ)*(base49) + (1535010418349/200000000000 : ℝ)*(major_s2_0) + (1535010418349/200000000000 : ℝ)*(major_s2_1) + (1535010418349/200000000000 : ℝ)*(major_s2_2) + (123997689/1000000000000 : ℝ)*(sp_s2_0) + (10073873/50000000000 : ℝ)*(sp_s2_2) + (296021293/1000000000000 : ℝ)*(sp_s2_6) + (11107699/50000000000 : ℝ)*(sp_s2_7) + (227223139/1000000000000 : ℝ)*(sp_s2_15) + (10412376561389/1000000000000 : ℝ)*(sp_s2_21) + (5206247744959/500000000000 : ℝ)*(sp_s2_22) + (5206260617799/500000000000 : ℝ)*(sp_s2_23) + (4937079880453/1000000000000 : ℝ)*(sp_s2_27) + (987475180349/200000000000 : ℝ)*(f.failure) + (10412722713057/1000000000000 : ℝ)*(f.sum) + (4970613244353167221/10369823400000000000000000000000 : ℝ)*base62 + (894851619656197/1182420000000000000000000000 : ℝ)*base65 + (227363659494617/263100000000000000000000000 : ℝ)*base66 + (42676205239789/295605000000000000000000000 : ℝ)*base68 + (6217012747161997391/16936984080000000000000000000000 : ℝ)*base71 + (157015223616279/286480000000000000000000000 : ℝ)*base72 + (543091831202183/526200000000000000000000000 : ℝ)*base74 + (191672045836883/286480000000000000000000000 : ℝ)*base77 + (990132574216421233/3768644400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (1081/2500000000000000 : ℝ)*base86 + (1081/2500000000000000 : ℝ)*base88 + (1081/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((3581/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3581/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7893/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7893/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59121/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59121/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16073/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16073/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3241/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3241/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21469/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21469/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307075_s2 p hpa hpb X hX hprev1

#print axioms solution

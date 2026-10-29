-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306061_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:58:49.214244+00:00
-- url     : https://prove2.me/submissions/d9a26236-5a04-4b49-a5b0-4c640e418a26

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
theorem collision_support_c306061_s5_s5_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-284719221/1250000000 : ℝ)*x 0 + (2282638157/5000000000 : ℝ)*x 1 + (235112807/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284719221/1250000000 : ℝ)^135 ≤ (14384581385033/100000000000000 : ℝ)^103 := by
    have hnat : (284719221 : ℕ)^135*100000000000000^103 ≤ 14384581385033^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284719221 1250000000 14384581385033 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282638157/5000000000 : ℝ)^135 ≤ (17891239680677/50000000000000 : ℝ)^103 := by
    have hnat : (2282638157 : ℕ)^135*50000000000000^103 ≤ 17891239680677^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282638157 5000000000 17891239680677 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235112807/400000000 : ℝ)^135 ≤ (49832939240423/100000000000000 : ℝ)^103 := by
    have hnat : (235112807 : ℕ)^135*100000000000000^103 ≤ 49832939240423^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235112807 400000000 49832939240423 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-284719221/1250000000 : ℝ), (2282638157/5000000000 : ℝ), (235112807/400000000 : ℝ)] ![(14384581385033/100000000000000 : ℝ), (17891239680677/50000000000000 : ℝ), (49832939240423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-284719221/1250000000 : ℝ)|^135 ≤ (14384581385033/100000000000000 : ℝ)^103
        have hw : |(-284719221/1250000000 : ℝ)|=(284719221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282638157/5000000000 : ℝ)|^135 ≤ (17891239680677/50000000000000 : ℝ)^103
        have hw : |(2282638157/5000000000 : ℝ)|=(2282638157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(235112807/400000000 : ℝ)|^135 ≤ (49832939240423/100000000000000 : ℝ)^103
        have hw : |(235112807/400000000 : ℝ)|=(235112807/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (236497589/500000000 : ℝ)*x 0 + (-478043681/2000000000 : ℝ)*x 1 + (563879991/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236497589/500000000 : ℝ)^135 ≤ (1171362576937/3125000000000 : ℝ)^103 := by
    have hnat : (236497589 : ℕ)^135*3125000000000^103 ≤ 1171362576937^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236497589 500000000 1171362576937 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478043681/2000000000 : ℝ)^135 ≤ (7661270936699/50000000000000 : ℝ)^103 := by
    have hnat : (478043681 : ℕ)^135*50000000000000^103 ≤ 7661270936699^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478043681 2000000000 7661270936699 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563879991/1000000000 : ℝ)^135 ≤ (47193855644781/100000000000000 : ℝ)^103 := by
    have hnat : (563879991 : ℕ)^135*100000000000000^103 ≤ 47193855644781^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563879991 1000000000 47193855644781 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(236497589/500000000 : ℝ), (-478043681/2000000000 : ℝ), (563879991/1000000000 : ℝ)] ![(1171362576937/3125000000000 : ℝ), (7661270936699/50000000000000 : ℝ), (47193855644781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(236497589/500000000 : ℝ)|^135 ≤ (1171362576937/3125000000000 : ℝ)^103
        have hw : |(236497589/500000000 : ℝ)|=(236497589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478043681/2000000000 : ℝ)|^135 ≤ (7661270936699/50000000000000 : ℝ)^103
        have hw : |(-478043681/2000000000 : ℝ)|=(478043681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563879991/1000000000 : ℝ)|^135 ≤ (47193855644781/100000000000000 : ℝ)^103
        have hw : |(563879991/1000000000 : ℝ)|=(563879991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (150696349/312500000 : ℝ)*x 0 + (3124158013/5000000000 : ℝ)*x 1 + (-174370917/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (150696349/312500000 : ℝ)^135 ≤ (7689104780719/20000000000000 : ℝ)^103 := by
    have hnat : (150696349 : ℕ)^135*20000000000000^103 ≤ 7689104780719^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150696349 312500000 7689104780719 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3124158013/5000000000 : ℝ)^135 ≤ (843588668087/1562500000000 : ℝ)^103 := by
    have hnat : (3124158013 : ℕ)^135*1562500000000^103 ≤ 843588668087^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3124158013 5000000000 843588668087 1562500000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174370917/1250000000 : ℝ)^135 ≤ (3782400658513/50000000000000 : ℝ)^103 := by
    have hnat : (174370917 : ℕ)^135*50000000000000^103 ≤ 3782400658513^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174370917 1250000000 3782400658513 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(150696349/312500000 : ℝ), (3124158013/5000000000 : ℝ), (-174370917/1250000000 : ℝ)] ![(7689104780719/20000000000000 : ℝ), (843588668087/1562500000000 : ℝ), (3782400658513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(150696349/312500000 : ℝ)|^135 ≤ (7689104780719/20000000000000 : ℝ)^103
        have hw : |(150696349/312500000 : ℝ)|=(150696349/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3124158013/5000000000 : ℝ)|^135 ≤ (843588668087/1562500000000 : ℝ)^103
        have hw : |(3124158013/5000000000 : ℝ)|=(3124158013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-174370917/1250000000 : ℝ)|^135 ≤ (3782400658513/50000000000000 : ℝ)^103
        have hw : |(-174370917/1250000000 : ℝ)|=(174370917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2994812553/5000000000 : ℝ)*x 0 + (97001917/312500000 : ℝ)*x 1 + (3717844271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2994812553/5000000000 : ℝ)^135 ≤ (25539491825617/50000000000000 : ℝ)^103 := by
    have hnat : (2994812553 : ℕ)^135*50000000000000^103 ≤ 25539491825617^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2994812553 5000000000 25539491825617 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97001917/312500000 : ℝ)^135 ≤ (10790793986403/50000000000000 : ℝ)^103 := by
    have hnat : (97001917 : ℕ)^135*50000000000000^103 ≤ 10790793986403^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97001917 312500000 10790793986403 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3717844271/10000000000 : ℝ)^135 ≤ (5467885673299/20000000000000 : ℝ)^103 := by
    have hnat : (3717844271 : ℕ)^135*20000000000000^103 ≤ 5467885673299^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3717844271 10000000000 5467885673299 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2994812553/5000000000 : ℝ), (97001917/312500000 : ℝ), (3717844271/10000000000 : ℝ)] ![(25539491825617/50000000000000 : ℝ), (10790793986403/50000000000000 : ℝ), (5467885673299/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2994812553/5000000000 : ℝ)|^135 ≤ (25539491825617/50000000000000 : ℝ)^103
        have hw : |(2994812553/5000000000 : ℝ)|=(2994812553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97001917/312500000 : ℝ)|^135 ≤ (10790793986403/50000000000000 : ℝ)^103
        have hw : |(97001917/312500000 : ℝ)|=(97001917/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3717844271/10000000000 : ℝ)|^135 ≤ (5467885673299/20000000000000 : ℝ)^103
        have hw : |(3717844271/10000000000 : ℝ)|=(3717844271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1125508139/5000000000 : ℝ)*x 0 + (3878193721/10000000000 : ℝ)*x 1 + (6507278409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125508139/5000000000 : ℝ)^135 ≤ (7081836337371/50000000000000 : ℝ)^103 := by
    have hnat : (1125508139 : ℕ)^135*50000000000000^103 ≤ 7081836337371^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125508139 5000000000 7081836337371 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3878193721/10000000000 : ℝ)^135 ≤ (5779031570669/20000000000000 : ℝ)^103 := by
    have hnat : (3878193721 : ℕ)^135*20000000000000^103 ≤ 5779031570669^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3878193721 10000000000 5779031570669 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6507278409/10000000000 : ℝ)^135 ≤ (56941169459019/100000000000000 : ℝ)^103 := by
    have hnat : (6507278409 : ℕ)^135*100000000000000^103 ≤ 56941169459019^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6507278409 10000000000 56941169459019 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1125508139/5000000000 : ℝ), (3878193721/10000000000 : ℝ), (6507278409/10000000000 : ℝ)] ![(7081836337371/50000000000000 : ℝ), (5779031570669/20000000000000 : ℝ), (56941169459019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1125508139/5000000000 : ℝ)|^135 ≤ (7081836337371/50000000000000 : ℝ)^103
        have hw : |(-1125508139/5000000000 : ℝ)|=(1125508139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3878193721/10000000000 : ℝ)|^135 ≤ (5779031570669/20000000000000 : ℝ)^103
        have hw : |(3878193721/10000000000 : ℝ)|=(3878193721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6507278409/10000000000 : ℝ)|^135 ≤ (56941169459019/100000000000000 : ℝ)^103
        have hw : |(6507278409/10000000000 : ℝ)|=(6507278409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4327617461/10000000000 : ℝ)*x 0 + (-908245411/5000000000 : ℝ)*x 1 + (40127153/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327617461/10000000000 : ℝ)^135 ≤ (33360980233277/100000000000000 : ℝ)^103 := by
    have hnat : (4327617461 : ℕ)^135*100000000000000^103 ≤ 33360980233277^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327617461 10000000000 33360980233277 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908245411/5000000000 : ℝ)^135 ≤ (2673203845889/25000000000000 : ℝ)^103 := by
    have hnat : (908245411 : ℕ)^135*25000000000000^103 ≤ 2673203845889^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908245411 5000000000 2673203845889 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40127153/62500000 : ℝ)^135 ≤ (55946204359211/100000000000000 : ℝ)^103 := by
    have hnat : (40127153 : ℕ)^135*100000000000000^103 ≤ 55946204359211^103*62500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40127153 62500000 55946204359211 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327617461/10000000000 : ℝ), (-908245411/5000000000 : ℝ), (40127153/62500000 : ℝ)] ![(33360980233277/100000000000000 : ℝ), (2673203845889/25000000000000 : ℝ), (55946204359211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327617461/10000000000 : ℝ)|^135 ≤ (33360980233277/100000000000000 : ℝ)^103
        have hw : |(4327617461/10000000000 : ℝ)|=(4327617461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-908245411/5000000000 : ℝ)|^135 ≤ (2673203845889/25000000000000 : ℝ)^103
        have hw : |(-908245411/5000000000 : ℝ)|=(908245411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40127153/62500000 : ℝ)|^135 ≤ (55946204359211/100000000000000 : ℝ)^103
        have hw : |(40127153/62500000 : ℝ)|=(40127153/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2210343141/5000000000 : ℝ)*x 0 + (7012501081/10000000000 : ℝ)*x 1 + (-334845011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210343141/5000000000 : ℝ)^135 ≤ (34304458813469/100000000000000 : ℝ)^103 := by
    have hnat : (2210343141 : ℕ)^135*100000000000000^103 ≤ 34304458813469^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210343141 5000000000 34304458813469 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7012501081/10000000000 : ℝ)^135 ≤ (31402108568607/50000000000000 : ℝ)^103 := by
    have hnat : (7012501081 : ℕ)^135*50000000000000^103 ≤ 31402108568607^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7012501081 10000000000 31402108568607 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334845011/5000000000 : ℝ)^135 ≤ (578264805329/20000000000000 : ℝ)^103 := by
    have hnat : (334845011 : ℕ)^135*20000000000000^103 ≤ 578264805329^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334845011 5000000000 578264805329 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2210343141/5000000000 : ℝ), (7012501081/10000000000 : ℝ), (-334845011/5000000000 : ℝ)] ![(34304458813469/100000000000000 : ℝ), (31402108568607/50000000000000 : ℝ), (578264805329/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2210343141/5000000000 : ℝ)|^135 ≤ (34304458813469/100000000000000 : ℝ)^103
        have hw : |(2210343141/5000000000 : ℝ)|=(2210343141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7012501081/10000000000 : ℝ)|^135 ≤ (31402108568607/50000000000000 : ℝ)^103
        have hw : |(7012501081/10000000000 : ℝ)|=(7012501081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-334845011/5000000000 : ℝ)|^135 ≤ (578264805329/20000000000000 : ℝ)^103
        have hw : |(-334845011/5000000000 : ℝ)|=(334845011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5895944529/10000000000 : ℝ)*x 0 + (34054559/78125000 : ℝ)*x 1 + (2504207167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5895944529/10000000000 : ℝ)^135 ≤ (50034435558687/100000000000000 : ℝ)^103 := by
    have hnat : (5895944529 : ℕ)^135*100000000000000^103 ≤ 50034435558687^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5895944529 10000000000 50034435558687 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34054559/78125000 : ℝ)^135 ≤ (33678254435177/100000000000000 : ℝ)^103 := by
    have hnat : (34054559 : ℕ)^135*100000000000000^103 ≤ 33678254435177^103*78125000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34054559 78125000 33678254435177 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2504207167/10000000000 : ℝ)^135 ≤ (16287309991227/100000000000000 : ℝ)^103 := by
    have hnat : (2504207167 : ℕ)^135*100000000000000^103 ≤ 16287309991227^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504207167 10000000000 16287309991227 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5895944529/10000000000 : ℝ), (34054559/78125000 : ℝ), (2504207167/10000000000 : ℝ)] ![(50034435558687/100000000000000 : ℝ), (33678254435177/100000000000000 : ℝ), (16287309991227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5895944529/10000000000 : ℝ)|^135 ≤ (50034435558687/100000000000000 : ℝ)^103
        have hw : |(5895944529/10000000000 : ℝ)|=(5895944529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34054559/78125000 : ℝ)|^135 ≤ (33678254435177/100000000000000 : ℝ)^103
        have hw : |(34054559/78125000 : ℝ)|=(34054559/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2504207167/10000000000 : ℝ)|^135 ≤ (16287309991227/100000000000000 : ℝ)^103
        have hw : |(2504207167/10000000000 : ℝ)|=(2504207167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-167716551/1250000000 : ℝ)*x 0 + (4581082439/10000000000 : ℝ)*x 1 + (1625188879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167716551/1250000000 : ℝ)^135 ≤ (359434282831/5000000000000 : ℝ)^103 := by
    have hnat : (167716551 : ℕ)^135*5000000000000^103 ≤ 359434282831^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167716551 1250000000 359434282831 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4581082439/10000000000 : ℝ)^135 ≤ (17972471961531/50000000000000 : ℝ)^103 := by
    have hnat : (4581082439 : ℕ)^135*50000000000000^103 ≤ 17972471961531^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581082439 10000000000 17972471961531 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625188879/2500000000 : ℝ)^135 ≤ (56866370397883/100000000000000 : ℝ)^103 := by
    have hnat : (1625188879 : ℕ)^135*100000000000000^103 ≤ 56866370397883^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625188879 2500000000 56866370397883 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-167716551/1250000000 : ℝ), (4581082439/10000000000 : ℝ), (1625188879/2500000000 : ℝ)] ![(359434282831/5000000000000 : ℝ), (17972471961531/50000000000000 : ℝ), (56866370397883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-167716551/1250000000 : ℝ)|^135 ≤ (359434282831/5000000000000 : ℝ)^103
        have hw : |(-167716551/1250000000 : ℝ)|=(167716551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4581082439/10000000000 : ℝ)|^135 ≤ (17972471961531/50000000000000 : ℝ)^103
        have hw : |(4581082439/10000000000 : ℝ)|=(4581082439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1625188879/2500000000 : ℝ)|^135 ≤ (56866370397883/100000000000000 : ℝ)^103
        have hw : |(1625188879/2500000000 : ℝ)|=(1625188879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2097534511/5000000000 : ℝ)*x 0 + (-998096563/5000000000 : ℝ)*x 1 + (6413822561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097534511/5000000000 : ℝ)^135 ≤ (32028149288237/100000000000000 : ℝ)^103 := by
    have hnat : (2097534511 : ℕ)^135*100000000000000^103 ≤ 32028149288237^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097534511 5000000000 32028149288237 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998096563/5000000000 : ℝ)^135 ≤ (1512515279219/12500000000000 : ℝ)^103 := by
    have hnat : (998096563 : ℕ)^135*12500000000000^103 ≤ 1512515279219^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998096563 5000000000 1512515279219 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6413822561/10000000000 : ℝ)^135 ≤ (55871728471337/100000000000000 : ℝ)^103 := by
    have hnat : (6413822561 : ℕ)^135*100000000000000^103 ≤ 55871728471337^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6413822561 10000000000 55871728471337 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097534511/5000000000 : ℝ), (-998096563/5000000000 : ℝ), (6413822561/10000000000 : ℝ)] ![(32028149288237/100000000000000 : ℝ), (1512515279219/12500000000000 : ℝ), (55871728471337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097534511/5000000000 : ℝ)|^135 ≤ (32028149288237/100000000000000 : ℝ)^103
        have hw : |(2097534511/5000000000 : ℝ)|=(2097534511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-998096563/5000000000 : ℝ)|^135 ≤ (1512515279219/12500000000000 : ℝ)^103
        have hw : |(-998096563/5000000000 : ℝ)|=(998096563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6413822561/10000000000 : ℝ)|^135 ≤ (55871728471337/100000000000000 : ℝ)^103
        have hw : |(6413822561/10000000000 : ℝ)|=(6413822561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1453775381/2500000000 : ℝ)*x 0 + (228247883/400000000 : ℝ)*x 1 + (-676212259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1453775381/2500000000 : ℝ)^135 ≤ (49137160381867/100000000000000 : ℝ)^103 := by
    have hnat : (1453775381 : ℕ)^135*100000000000000^103 ≤ 49137160381867^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1453775381 2500000000 49137160381867 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228247883/400000000 : ℝ)^135 ≤ (23967276119961/50000000000000 : ℝ)^103 := by
    have hnat : (228247883 : ℕ)^135*50000000000000^103 ≤ 23967276119961^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228247883 400000000 23967276119961 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676212259/10000000000 : ℝ)^135 ≤ (2928287360503/100000000000000 : ℝ)^103 := by
    have hnat : (676212259 : ℕ)^135*100000000000000^103 ≤ 2928287360503^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676212259 10000000000 2928287360503 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1453775381/2500000000 : ℝ), (228247883/400000000 : ℝ), (-676212259/10000000000 : ℝ)] ![(49137160381867/100000000000000 : ℝ), (23967276119961/50000000000000 : ℝ), (2928287360503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1453775381/2500000000 : ℝ)|^135 ≤ (49137160381867/100000000000000 : ℝ)^103
        have hw : |(1453775381/2500000000 : ℝ)|=(1453775381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228247883/400000000 : ℝ)|^135 ≤ (23967276119961/50000000000000 : ℝ)^103
        have hw : |(228247883/400000000 : ℝ)|=(228247883/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-676212259/10000000000 : ℝ)|^135 ≤ (2928287360503/100000000000000 : ℝ)^103
        have hw : |(-676212259/10000000000 : ℝ)|=(676212259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1795753057/2500000000 : ℝ)*x 0 + (1396006797/5000000000 : ℝ)*x 1 + (314724813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1795753057/2500000000 : ℝ)^135 ≤ (506353747111/781250000000 : ℝ)^103 := by
    have hnat : (1795753057 : ℕ)^135*781250000000^103 ≤ 506353747111^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795753057 2500000000 506353747111 781250000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1396006797/5000000000 : ℝ)^135 ≤ (4695862913907/25000000000000 : ℝ)^103 := by
    have hnat : (1396006797 : ℕ)^135*25000000000000^103 ≤ 4695862913907^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396006797 5000000000 4695862913907 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314724813/1250000000 : ℝ)^135 ≤ (3280653740143/20000000000000 : ℝ)^103 := by
    have hnat : (314724813 : ℕ)^135*20000000000000^103 ≤ 3280653740143^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314724813 1250000000 3280653740143 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1795753057/2500000000 : ℝ), (1396006797/5000000000 : ℝ), (314724813/1250000000 : ℝ)] ![(506353747111/781250000000 : ℝ), (4695862913907/25000000000000 : ℝ), (3280653740143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1795753057/2500000000 : ℝ)|^135 ≤ (506353747111/781250000000 : ℝ)^103
        have hw : |(1795753057/2500000000 : ℝ)|=(1795753057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1396006797/5000000000 : ℝ)|^135 ≤ (4695862913907/25000000000000 : ℝ)^103
        have hw : |(1396006797/5000000000 : ℝ)|=(1396006797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314724813/1250000000 : ℝ)|^135 ≤ (3280653740143/20000000000000 : ℝ)^103
        have hw : |(314724813/1250000000 : ℝ)|=(314724813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-654467707/5000000000 : ℝ)*x 0 + (5269009403/10000000000 : ℝ)*x 1 + (5880383177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654467707/5000000000 : ℝ)^135 ≤ (6959254402437/100000000000000 : ℝ)^103 := by
    have hnat : (654467707 : ℕ)^135*100000000000000^103 ≤ 6959254402437^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654467707 5000000000 6959254402437 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5269009403/10000000000 : ℝ)^135 ≤ (21589662015101/50000000000000 : ℝ)^103 := by
    have hnat : (5269009403 : ℕ)^135*50000000000000^103 ≤ 21589662015101^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5269009403 10000000000 21589662015101 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5880383177/10000000000 : ℝ)^135 ≤ (12465355385987/25000000000000 : ℝ)^103 := by
    have hnat : (5880383177 : ℕ)^135*25000000000000^103 ≤ 12465355385987^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5880383177 10000000000 12465355385987 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-654467707/5000000000 : ℝ), (5269009403/10000000000 : ℝ), (5880383177/10000000000 : ℝ)] ![(6959254402437/100000000000000 : ℝ), (21589662015101/50000000000000 : ℝ), (12465355385987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-654467707/5000000000 : ℝ)|^135 ≤ (6959254402437/100000000000000 : ℝ)^103
        have hw : |(-654467707/5000000000 : ℝ)|=(654467707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5269009403/10000000000 : ℝ)|^135 ≤ (21589662015101/50000000000000 : ℝ)^103
        have hw : |(5269009403/10000000000 : ℝ)|=(5269009403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5880383177/10000000000 : ℝ)|^135 ≤ (12465355385987/25000000000000 : ℝ)^103
        have hw : |(5880383177/10000000000 : ℝ)|=(5880383177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2877414397/5000000000 : ℝ)*x 0 + (-712428533/5000000000 : ℝ)*x 1 + (5322181647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2877414397/5000000000 : ℝ)^135 ≤ (48470708690303/100000000000000 : ℝ)^103 := by
    have hnat : (2877414397 : ℕ)^135*100000000000000^103 ≤ 48470708690303^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2877414397 5000000000 48470708690303 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (712428533/5000000000 : ℝ)^135 ≤ (194448817029/2500000000000 : ℝ)^103 := by
    have hnat : (712428533 : ℕ)^135*2500000000000^103 ≤ 194448817029^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712428533 5000000000 194448817029 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5322181647/10000000000 : ℝ)^135 ≤ (21875669306931/50000000000000 : ℝ)^103 := by
    have hnat : (5322181647 : ℕ)^135*50000000000000^103 ≤ 21875669306931^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322181647 10000000000 21875669306931 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2877414397/5000000000 : ℝ), (-712428533/5000000000 : ℝ), (5322181647/10000000000 : ℝ)] ![(48470708690303/100000000000000 : ℝ), (194448817029/2500000000000 : ℝ), (21875669306931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2877414397/5000000000 : ℝ)|^135 ≤ (48470708690303/100000000000000 : ℝ)^103
        have hw : |(2877414397/5000000000 : ℝ)|=(2877414397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-712428533/5000000000 : ℝ)|^135 ≤ (194448817029/2500000000000 : ℝ)^103
        have hw : |(-712428533/5000000000 : ℝ)|=(712428533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5322181647/10000000000 : ℝ)|^135 ≤ (21875669306931/50000000000000 : ℝ)^103
        have hw : |(5322181647/10000000000 : ℝ)|=(5322181647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4180741423/10000000000 : ℝ)*x 0 + (434168507/625000000 : ℝ)*x 1 + (-590549313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180741423/10000000000 : ℝ)^135 ≤ (31884853956283/100000000000000 : ℝ)^103 := by
    have hnat : (4180741423 : ℕ)^135*100000000000000^103 ≤ 31884853956283^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180741423 10000000000 31884853956283 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434168507/625000000 : ℝ)^135 ≤ (6203289429661/10000000000000 : ℝ)^103 := by
    have hnat : (434168507 : ℕ)^135*10000000000000^103 ≤ 6203289429661^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434168507 625000000 6203289429661 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (590549313/5000000000 : ℝ)^135 ≤ (1216450344549/20000000000000 : ℝ)^103 := by
    have hnat : (590549313 : ℕ)^135*20000000000000^103 ≤ 1216450344549^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590549313 5000000000 1216450344549 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180741423/10000000000 : ℝ), (434168507/625000000 : ℝ), (-590549313/5000000000 : ℝ)] ![(31884853956283/100000000000000 : ℝ), (6203289429661/10000000000000 : ℝ), (1216450344549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180741423/10000000000 : ℝ)|^135 ≤ (31884853956283/100000000000000 : ℝ)^103
        have hw : |(4180741423/10000000000 : ℝ)|=(4180741423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(434168507/625000000 : ℝ)|^135 ≤ (6203289429661/10000000000000 : ℝ)^103
        have hw : |(434168507/625000000 : ℝ)|=(434168507/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-590549313/5000000000 : ℝ)|^135 ≤ (1216450344549/20000000000000 : ℝ)^103
        have hw : |(-590549313/5000000000 : ℝ)|=(590549313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306061_s5_s5_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (231462491/312500000 : ℝ)*x 0 + (1207043177/5000000000 : ℝ)*x 1 + (517569853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231462491/312500000 : ℝ)^135 ≤ (13494521277393/20000000000000 : ℝ)^103 := by
    have hnat : (231462491 : ℕ)^135*20000000000000^103 ≤ 13494521277393^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231462491 312500000 13494521277393 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1207043177/5000000000 : ℝ)^135 ≤ (7761697011203/50000000000000 : ℝ)^103 := by
    have hnat : (1207043177 : ℕ)^135*50000000000000^103 ≤ 7761697011203^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207043177 5000000000 7761697011203 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517569853/2000000000 : ℝ)^135 ≤ (17003999574617/100000000000000 : ℝ)^103 := by
    have hnat : (517569853 : ℕ)^135*100000000000000^103 ≤ 17003999574617^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517569853 2000000000 17003999574617 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(231462491/312500000 : ℝ), (1207043177/5000000000 : ℝ), (517569853/2000000000 : ℝ)] ![(13494521277393/20000000000000 : ℝ), (7761697011203/50000000000000 : ℝ), (17003999574617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(231462491/312500000 : ℝ)|^135 ≤ (13494521277393/20000000000000 : ℝ)^103
        have hw : |(231462491/312500000 : ℝ)|=(231462491/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1207043177/5000000000 : ℝ)|^135 ≤ (7761697011203/50000000000000 : ℝ)^103
        have hw : |(1207043177/5000000000 : ℝ)|=(1207043177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517569853/2000000000 : ℝ)|^135 ≤ (17003999574617/100000000000000 : ℝ)^103
        have hw : |(517569853/2000000000 : ℝ)|=(517569853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306061_s5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((53513/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(53513/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6021/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6021/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27061/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27061/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((32993/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32993/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38499/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38499/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8799/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8799/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (53513/100000 : ℝ) ^ (67/16 : ℝ) ≤ (7293287157576872953/100000000000000000000 : ℝ) := by
    have hpowers : (53513/100000 : ℝ)^67 ≤ (7293287157576872953/100000000000000000000 : ℝ)^16 := by
      have hnat : (53513 : ℕ)^67*100000000000000000000^16 ≤ 7293287157576872953^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53513 100000 7293287157576872953 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (53513/100000 : ℝ)) (X := (7293287157576872953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner0a : (107293287157576872953/100000000000000000000 : ℝ) ≤ (5084765303111661/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (107293287157576872953/100000000000000000000 : ℝ)^16 ≤ (5084765303111661/5000000000000000 : ℝ)^67 := by
      have hnat : (107293287157576872953 : ℕ)^16*5000000000000000^67 ≤ 5084765303111661^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107293287157576872953 100000000000000000000 5084765303111661 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5084765303111661/5000000000000000 : ℝ)) (X := (107293287157576872953/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner0b : (57293287157576872953/50000000000000000000 : ℝ) ≤ (10330503499938771/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (57293287157576872953/50000000000000000000 : ℝ)^16 ≤ (10330503499938771/10000000000000000 : ℝ)^67 := by
      have hnat : (57293287157576872953 : ℕ)^16*10000000000000000^67 ≤ 10330503499938771^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57293287157576872953 50000000000000000000 10330503499938771 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10330503499938771/10000000000000000 : ℝ)) (X := (57293287157576872953/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(84765303111661/2675650000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(160972893715449/5351300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (53513/100000 : ℝ)) (alpha := (84765303111661/2675650000000000 : ℝ)) (beta := (160972893715449/5351300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (53513/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(84765303111661/2675650000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(160972893715449/5351300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (6021/10000 : ℝ) ^ (67/16 : ℝ) ≤ (11949847869613409321/100000000000000000000 : ℝ) := by
    have hpowers : (6021/10000 : ℝ)^67 ≤ (11949847869613409321/100000000000000000000 : ℝ)^16 := by
      have hnat : (6021 : ℕ)^67*100000000000000000000^16 ≤ 11949847869613409321^16*10000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6021 10000 11949847869613409321 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6021/10000 : ℝ)) (X := (11949847869613409321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner1a : (111949847869613409321/100000000000000000000 : ℝ) ≤ (10273232247124913/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (111949847869613409321/100000000000000000000 : ℝ)^16 ≤ (10273232247124913/10000000000000000 : ℝ)^67 := by
      have hnat : (111949847869613409321 : ℕ)^16*10000000000000000^67 ≤ 10273232247124913^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111949847869613409321 100000000000000000000 10273232247124913 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10273232247124913/10000000000000000 : ℝ)) (X := (111949847869613409321/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner1b : (61949847869613409321/50000000000000000000 : ℝ) ≤ (657817989818511/625000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (61949847869613409321/50000000000000000000 : ℝ)^16 ≤ (657817989818511/625000000000000 : ℝ)^67 := by
      have hnat : (61949847869613409321 : ℕ)^16*625000000000000^67 ≤ 657817989818511^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61949847869613409321 50000000000000000000 657817989818511 625000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (657817989818511/625000000000000 : ℝ)) (X := (61949847869613409321/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(273232247124913/6021000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(251855589971263/6021000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (6021/10000 : ℝ)) (alpha := (273232247124913/6021000000000000 : ℝ)) (beta := (251855589971263/6021000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6021/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(273232247124913/6021000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(251855589971263/6021000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (27061/50000 : ℝ) ^ (67/16 : ℝ) ≤ (1529441738320299257/20000000000000000000 : ℝ) := by
    have hpowers : (27061/50000 : ℝ)^67 ≤ (1529441738320299257/20000000000000000000 : ℝ)^16 := by
      have hnat : (27061 : ℕ)^67*20000000000000000000^16 ≤ 1529441738320299257^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27061 50000 1529441738320299257 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27061/50000 : ℝ)) (X := (1529441738320299257/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner2a : (21529441738320299257/20000000000000000000 : ℝ) ≤ (5088765726939269/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (21529441738320299257/20000000000000000000 : ℝ)^16 ≤ (5088765726939269/5000000000000000 : ℝ)^67 := by
      have hnat : (21529441738320299257 : ℕ)^16*5000000000000000^67 ≤ 5088765726939269^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21529441738320299257 20000000000000000000 5088765726939269 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5088765726939269/5000000000000000 : ℝ)) (X := (21529441738320299257/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner2b : (11529441738320299257/10000000000000000000 : ℝ) ≤ (258642681796807/250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (11529441738320299257/10000000000000000000 : ℝ)^16 ≤ (258642681796807/250000000000000 : ℝ)^67 := by
      have hnat : (11529441738320299257 : ℕ)^16*250000000000000^67 ≤ 258642681796807^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11529441738320299257 10000000000000000000 258642681796807 250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (258642681796807/250000000000000 : ℝ)) (X := (11529441738320299257/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(88765726939269/2706100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(84087908996871/2706100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (27061/50000 : ℝ)) (alpha := (88765726939269/2706100000000000 : ℝ)) (beta := (84087908996871/2706100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (27061/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(88765726939269/2706100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(84087908996871/2706100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-284719221/1250000000 : ℝ)*X 0 0+(2282638157/5000000000 : ℝ)*X 0 1+(235112807/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((236497589/500000000 : ℝ)*X 1 0+(-478043681/2000000000 : ℝ)*X 1 1+(563879991/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((150696349/312500000 : ℝ)*X 2 0+(3124158013/5000000000 : ℝ)*X 2 1+(-174370917/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((2994812553/5000000000 : ℝ)*X 0 0+(97001917/312500000 : ℝ)*X 0 1+(3717844271/10000000000 : ℝ)*X 0 2+(2994812553/5000000000 : ℝ)*X 1 0+(97001917/312500000 : ℝ)*X 1 1+(3717844271/10000000000 : ℝ)*X 1 2+(2994812553/5000000000 : ℝ)*X 2 0+(97001917/312500000 : ℝ)*X 2 1+(3717844271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-1125508139/5000000000 : ℝ)*X 0 0+(3878193721/10000000000 : ℝ)*X 0 1+(6507278409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((4327617461/10000000000 : ℝ)*X 1 0+(-908245411/5000000000 : ℝ)*X 1 1+(40127153/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((2210343141/5000000000 : ℝ)*X 2 0+(7012501081/10000000000 : ℝ)*X 2 1+(-334845011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((5895944529/10000000000 : ℝ)*X 0 0+(34054559/78125000 : ℝ)*X 0 1+(2504207167/10000000000 : ℝ)*X 0 2+(5895944529/10000000000 : ℝ)*X 1 0+(34054559/78125000 : ℝ)*X 1 1+(2504207167/10000000000 : ℝ)*X 1 2+(5895944529/10000000000 : ℝ)*X 2 0+(34054559/78125000 : ℝ)*X 2 1+(2504207167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-167716551/1250000000 : ℝ)*X 0 0+(4581082439/10000000000 : ℝ)*X 0 1+(1625188879/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((2097534511/5000000000 : ℝ)*X 1 0+(-998096563/5000000000 : ℝ)*X 1 1+(6413822561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((1453775381/2500000000 : ℝ)*X 2 0+(228247883/400000000 : ℝ)*X 2 1+(-676212259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((1795753057/2500000000 : ℝ)*X 0 0+(1396006797/5000000000 : ℝ)*X 0 1+(314724813/1250000000 : ℝ)*X 0 2+(1795753057/2500000000 : ℝ)*X 1 0+(1396006797/5000000000 : ℝ)*X 1 1+(314724813/1250000000 : ℝ)*X 1 2+(1795753057/2500000000 : ℝ)*X 2 0+(1396006797/5000000000 : ℝ)*X 2 1+(314724813/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-654467707/5000000000 : ℝ)*X 0 0+(5269009403/10000000000 : ℝ)*X 0 1+(5880383177/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((2877414397/5000000000 : ℝ)*X 1 0+(-712428533/5000000000 : ℝ)*X 1 1+(5322181647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((4180741423/10000000000 : ℝ)*X 2 0+(434168507/625000000 : ℝ)*X 2 1+(-590549313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((231462491/312500000 : ℝ)*X 0 0+(1207043177/5000000000 : ℝ)*X 0 1+(517569853/2000000000 : ℝ)*X 0 2+(231462491/312500000 : ℝ)*X 1 0+(1207043177/5000000000 : ℝ)*X 1 1+(517569853/2000000000 : ℝ)*X 1 2+(231462491/312500000 : ℝ)*X 2 0+(1207043177/5000000000 : ℝ)*X 2 1+(517569853/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306061_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((32993/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32993/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (484136093855301156587022847111/30274660344281250000000000000000000 : ℝ) := by norm_num
    linear_combination (79453/50000000000 : ℝ)*(base50) + (407876481081/500000000000 : ℝ)*(base59) + (314513610393/62500000000 : ℝ)*(major_s5_0) + (314513610393/62500000000 : ℝ)*(major_s5_1) + (314513610393/62500000000 : ℝ)*(major_s5_2) + (51889857/1000000000000 : ℝ)*(sp_s5_0) + (2487377/200000000000 : ℝ)*(sp_s5_1) + (40872669/1000000000000 : ℝ)*(sp_s5_6) + (6800646348047/1000000000000 : ℝ)*(sp_s5_7) + (3400109805803/500000000000 : ℝ)*(sp_s5_8) + (136011297061/20000000000 : ℝ)*(sp_s5_9) + (3263691091509/1000000000000 : ℝ)*(sp_s5_13) + (466189413/1000000000000 : ℝ)*(sp_s5_15) + (66692427/500000000000 : ℝ)*(sp_s5_23) + (1631865982089/500000000000 : ℝ)*(f.failure) + (425043639869/62500000000 : ℝ)*(f.sum) + (4901779608244744117/13577856750000000000000000000000 : ℝ)*base63 + (958322185080431/1353050000000000000000000000 : ℝ)*base65 + (11532624911789/62718750000000000000000000 : ℝ)*base67 + (625935457189001/1353050000000000000000000000 : ℝ)*base69 + (20694013484777531251/72405764650000000000000000000000 : ℝ)*base71 + (1355806182949531/2675650000000000000000000000 : ℝ)*base73 + (398633288928937/501750000000000000000000000 : ℝ)*base75 + (602662732916119/1337825000000000000000000000 : ℝ)*base77 + (2970991115576080967/13425073875000000000000000000000 : ℝ)*base78 + (12723/25000000000000000 : ℝ)*base86 + (12723/25000000000000000 : ℝ)*base88 + (12723/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38499/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38499/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16434529408184508204710887/3017301500000000000000000000000 : ℝ) := by norm_num
    linear_combination (381391/1000000000000 : ℝ)*(base39) + (178023/1000000000000 : ℝ)*(base49) + (216367548267/500000000000 : ℝ)*(base59) + (4845939589521/1000000000000 : ℝ)*(major_s5_0) + (4845939589521/1000000000000 : ℝ)*(major_s5_1) + (4845939589521/1000000000000 : ℝ)*(major_s5_2) + (3726607/250000000000 : ℝ)*(sp_s5_2) + (3222907/500000000000 : ℝ)*(sp_s5_6) + (29683111/1000000000000 : ℝ)*(sp_s5_7) + (6548929653071/1000000000000 : ℝ)*(sp_s5_14) + (3274479668091/500000000000 : ℝ)*(sp_s5_15) + (6548944429753/1000000000000 : ℝ)*(sp_s5_16) + (3142831879531/1000000000000 : ℝ)*(sp_s5_20) + (39850961/500000000000 : ℝ)*(sp_s5_27) + (3142918027267/1000000000000 : ℝ)*(f.failure) + (3274479668091/500000000000 : ℝ)*(f.sum) + (4444836060602971073/18103809000000000000000000000000 : ℝ)*base62 + (2087997952429771/2706100000000000000000000000 : ℝ)*base64 + (344615550343253/669000000000000000000000000 : ℝ)*base66 + (1656859085810051/2706100000000000000000000000 : ℝ)*base68 + (55204623118801610281/144811529300000000000000000000000 : ℝ)*base70 + (1668203781084571/5351300000000000000000000000 : ℝ)*base72 + (81589672608503/669000000000000000000000000 : ℝ)*base74 + (46773944297379/668912500000000000000000000 : ℝ)*base77 + (1777394092317966221/35800197000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (44831/50000000000000000 : ℝ)*base87 + (44831/50000000000000000 : ℝ)*base89 + (44831/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8799/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8799/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (395254880355928079128301549/27155713500000000000000000000000 : ℝ) := by norm_num
    linear_combination (8428171/1000000000000 : ℝ)*(base15) + (56537052887/200000000000 : ℝ)*(base40) + (222548515819/500000000000 : ℝ)*(base59) + (4438480209307/1000000000000 : ℝ)*(major_s5_0) + (4438480209307/1000000000000 : ℝ)*(major_s5_1) + (4438480209307/1000000000000 : ℝ)*(major_s5_2) + (826051/200000000000 : ℝ)*(sp_s5_1) + (202830827/1000000000000 : ℝ)*(sp_s5_2) + (4226691/62500000000 : ℝ)*(sp_s5_9) + (563833117/1000000000000 : ℝ)*(sp_s5_20) + (1499575593937/250000000000 : ℝ)*(sp_s5_21) + (2999144908661/500000000000 : ℝ)*(sp_s5_22) + (749753989733/125000000000 : ℝ)*(sp_s5_23) + (2878089358033/1000000000000 : ℝ)*(sp_s5_27) + (57573063823/20000000000 : ℝ)*(f.failure) + (1499575593937/250000000000 : ℝ)*(f.sum) + (13688825718900852181/162934281000000000000000000000000 : ℝ)*base63 + (379638657459037/2706100000000000000000000000 : ℝ)*base64 + (1887703487115841/6021000000000000000000000000 : ℝ)*base67 + (620445965785183/2706100000000000000000000000 : ℝ)*base69 + (43537731472241424857/144811529300000000000000000000000 : ℝ)*base70 + (1583733575106233/5351300000000000000000000000 : ℝ)*base73 + (4856403317484091/6021000000000000000000000000 : ℝ)*base75 + (2906047707674837/2675650000000000000000000000 : ℝ)*base77 + (55940759567742876337/322201773000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (461/1000000000000000 : ℝ)*base86 + (461/1000000000000000 : ℝ)*base88 + (461/1000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((53513/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(53513/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6021/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6021/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27061/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27061/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((32993/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32993/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38499/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38499/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8799/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8799/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306061_s5 p hpa hpb X hX hprev4

#print axioms solution

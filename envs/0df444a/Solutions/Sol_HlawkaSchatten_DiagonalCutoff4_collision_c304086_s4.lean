-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304086_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:50:44.492969+00:00
-- url     : https://prove2.me/submissions/edc1b552-4e4d-43d1-b1ab-9679be9cc954

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
theorem collision_support_c304086_s4_s4_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-568121673/10000000000 : ℝ)*x 0 + (-380341563/625000000 : ℝ)*x 1 + (689872917/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (568121673/10000000000 : ℝ)^133 ≤ (9159439689/400000000000 : ℝ)^101 := by
    have hnat : (568121673 : ℕ)^133*400000000000^101 ≤ 9159439689^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568121673 10000000000 9159439689 400000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (380341563/625000000 : ℝ)^133 ≤ (25996878580969/50000000000000 : ℝ)^101 := by
    have hnat : (380341563 : ℕ)^133*50000000000000^101 ≤ 25996878580969^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380341563 625000000 25996878580969 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689872917/1250000000 : ℝ)^133 ≤ (45716382893787/100000000000000 : ℝ)^101 := by
    have hnat : (689872917 : ℕ)^133*100000000000000^101 ≤ 45716382893787^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689872917 1250000000 45716382893787 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-568121673/10000000000 : ℝ), (-380341563/625000000 : ℝ), (689872917/1250000000 : ℝ)] ![(9159439689/400000000000 : ℝ), (25996878580969/50000000000000 : ℝ), (45716382893787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-568121673/10000000000 : ℝ)|^133 ≤ (9159439689/400000000000 : ℝ)^101
        have hw : |(-568121673/10000000000 : ℝ)|=(568121673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-380341563/625000000 : ℝ)|^133 ≤ (25996878580969/50000000000000 : ℝ)^101
        have hw : |(-380341563/625000000 : ℝ)|=(380341563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(689872917/1250000000 : ℝ)|^133 ≤ (45716382893787/100000000000000 : ℝ)^101
        have hw : |(689872917/1250000000 : ℝ)|=(689872917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1461549377/2500000000 : ℝ)*x 0 + (-182641071/500000000 : ℝ)*x 1 + (-424668917/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1461549377/2500000000 : ℝ)^133 ≤ (493186995941/1000000000000 : ℝ)^101 := by
    have hnat : (1461549377 : ℕ)^133*1000000000000^101 ≤ 493186995941^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461549377 2500000000 493186995941 1000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182641071/500000000 : ℝ)^133 ≤ (26549434407601/100000000000000 : ℝ)^101 := by
    have hnat : (182641071 : ℕ)^133*100000000000000^101 ≤ 26549434407601^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182641071 500000000 26549434407601 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424668917/1250000000 : ℝ)^133 ≤ (3016483248691/12500000000000 : ℝ)^101 := by
    have hnat : (424668917 : ℕ)^133*12500000000000^101 ≤ 3016483248691^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424668917 1250000000 3016483248691 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1461549377/2500000000 : ℝ), (-182641071/500000000 : ℝ), (-424668917/1250000000 : ℝ)] ![(493186995941/1000000000000 : ℝ), (26549434407601/100000000000000 : ℝ), (3016483248691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1461549377/2500000000 : ℝ)|^133 ≤ (493186995941/1000000000000 : ℝ)^101
        have hw : |(1461549377/2500000000 : ℝ)|=(1461549377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182641071/500000000 : ℝ)|^133 ≤ (26549434407601/100000000000000 : ℝ)^101
        have hw : |(-182641071/500000000 : ℝ)|=(182641071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424668917/1250000000 : ℝ)|^133 ≤ (3016483248691/12500000000000 : ℝ)^101
        have hw : |(-424668917/1250000000 : ℝ)|=(424668917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-154239139/10000000000 : ℝ)*x 0 + (-362239993/500000000 : ℝ)*x 1 + (2212355993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (154239139/10000000000 : ℝ)^133 ≤ (411298603859/100000000000000 : ℝ)^101 := by
    have hnat : (154239139 : ℕ)^133*100000000000000^101 ≤ 411298603859^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154239139 10000000000 411298603859 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (362239993/500000000 : ℝ)^133 ≤ (65415146561969/100000000000000 : ℝ)^101 := by
    have hnat : (362239993 : ℕ)^133*100000000000000^101 ≤ 65415146561969^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362239993 500000000 65415146561969 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212355993/5000000000 : ℝ)^133 ≤ (4271694351489/12500000000000 : ℝ)^101 := by
    have hnat : (2212355993 : ℕ)^133*12500000000000^101 ≤ 4271694351489^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212355993 5000000000 4271694351489 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-154239139/10000000000 : ℝ), (-362239993/500000000 : ℝ), (2212355993/5000000000 : ℝ)] ![(411298603859/100000000000000 : ℝ), (65415146561969/100000000000000 : ℝ), (4271694351489/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-154239139/10000000000 : ℝ)|^133 ≤ (411298603859/100000000000000 : ℝ)^101
        have hw : |(-154239139/10000000000 : ℝ)|=(154239139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-362239993/500000000 : ℝ)|^133 ≤ (65415146561969/100000000000000 : ℝ)^101
        have hw : |(-362239993/500000000 : ℝ)|=(362239993/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2212355993/5000000000 : ℝ)|^133 ≤ (4271694351489/12500000000000 : ℝ)^101
        have hw : |(2212355993/5000000000 : ℝ)|=(2212355993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3048150751/5000000000 : ℝ)*x 0 + (3409418381/10000000000 : ℝ)*x 1 + (13378323/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3048150751/5000000000 : ℝ)^133 ≤ (5211571197333/10000000000000 : ℝ)^101 := by
    have hnat : (3048150751 : ℕ)^133*10000000000000^101 ≤ 5211571197333^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3048150751 5000000000 5211571197333 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3409418381/10000000000 : ℝ)^133 ≤ (24244800258307/100000000000000 : ℝ)^101 := by
    have hnat : (3409418381 : ℕ)^133*100000000000000^101 ≤ 24244800258307^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3409418381 10000000000 24244800258307 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13378323/40000000 : ℝ)^133 ≤ (23639487752669/100000000000000 : ℝ)^101 := by
    have hnat : (13378323 : ℕ)^133*100000000000000^101 ≤ 23639487752669^101*40000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13378323 40000000 23639487752669 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3048150751/5000000000 : ℝ), (3409418381/10000000000 : ℝ), (13378323/40000000 : ℝ)] ![(5211571197333/10000000000000 : ℝ), (24244800258307/100000000000000 : ℝ), (23639487752669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3048150751/5000000000 : ℝ)|^133 ≤ (5211571197333/10000000000000 : ℝ)^101
        have hw : |(3048150751/5000000000 : ℝ)|=(3048150751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3409418381/10000000000 : ℝ)|^133 ≤ (24244800258307/100000000000000 : ℝ)^101
        have hw : |(3409418381/10000000000 : ℝ)|=(3409418381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13378323/40000000 : ℝ)|^133 ≤ (23639487752669/100000000000000 : ℝ)^101
        have hw : |(13378323/40000000 : ℝ)|=(13378323/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (602690753/1000000000 : ℝ)*x 0 + (-1740701581/5000000000 : ℝ)*x 1 + (-3355690069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (602690753/1000000000 : ℝ)^133 ≤ (51335938668857/100000000000000 : ℝ)^101 := by
    have hnat : (602690753 : ℕ)^133*100000000000000^101 ≤ 51335938668857^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602690753 1000000000 51335938668857 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1740701581/5000000000 : ℝ)^133 ≤ (24921120731783/100000000000000 : ℝ)^101 := by
    have hnat : (1740701581 : ℕ)^133*100000000000000^101 ≤ 24921120731783^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740701581 5000000000 24921120731783 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3355690069/10000000000 : ℝ)^133 ≤ (118714702907/500000000000 : ℝ)^101 := by
    have hnat : (3355690069 : ℕ)^133*500000000000^101 ≤ 118714702907^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3355690069 10000000000 118714702907 500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(602690753/1000000000 : ℝ), (-1740701581/5000000000 : ℝ), (-3355690069/10000000000 : ℝ)] ![(51335938668857/100000000000000 : ℝ), (24921120731783/100000000000000 : ℝ), (118714702907/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(602690753/1000000000 : ℝ)|^133 ≤ (51335938668857/100000000000000 : ℝ)^101
        have hw : |(602690753/1000000000 : ℝ)|=(602690753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1740701581/5000000000 : ℝ)|^133 ≤ (24921120731783/100000000000000 : ℝ)^101
        have hw : |(-1740701581/5000000000 : ℝ)|=(1740701581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3355690069/10000000000 : ℝ)|^133 ≤ (118714702907/500000000000 : ℝ)^101
        have hw : |(-3355690069/10000000000 : ℝ)|=(3355690069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1477719299/5000000000 : ℝ)*x 0 + (-1590460877/10000000000 : ℝ)*x 1 + (1928104737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1477719299/5000000000 : ℝ)^133 ≤ (20086219273577/100000000000000 : ℝ)^101 := by
    have hnat : (1477719299 : ℕ)^133*100000000000000^101 ≤ 20086219273577^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477719299 5000000000 20086219273577 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1590460877/10000000000 : ℝ)^133 ≤ (4441300718293/50000000000000 : ℝ)^101 := by
    have hnat : (1590460877 : ℕ)^133*50000000000000^101 ≤ 4441300718293^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590460877 10000000000 4441300718293 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1928104737/2500000000 : ℝ)^133 ≤ (71031179271643/100000000000000 : ℝ)^101 := by
    have hnat : (1928104737 : ℕ)^133*100000000000000^101 ≤ 71031179271643^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928104737 2500000000 71031179271643 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1477719299/5000000000 : ℝ), (-1590460877/10000000000 : ℝ), (1928104737/2500000000 : ℝ)] ![(20086219273577/100000000000000 : ℝ), (4441300718293/50000000000000 : ℝ), (71031179271643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1477719299/5000000000 : ℝ)|^133 ≤ (20086219273577/100000000000000 : ℝ)^101
        have hw : |(1477719299/5000000000 : ℝ)|=(1477719299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1590460877/10000000000 : ℝ)|^133 ≤ (4441300718293/50000000000000 : ℝ)^101
        have hw : |(-1590460877/10000000000 : ℝ)|=(1590460877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1928104737/2500000000 : ℝ)|^133 ≤ (71031179271643/100000000000000 : ℝ)^101
        have hw : |(1928104737/2500000000 : ℝ)|=(1928104737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-15019/10000000000 : ℝ)*x 0 + (-2877568847/5000000000 : ℝ)*x 1 + (6058479713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15019/10000000000 : ℝ)^133 ≤ (429187/20000000000000 : ℝ)^101 := by
    have hnat : (15019 : ℕ)^133*20000000000000^101 ≤ 429187^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15019 10000000000 429187 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2877568847/5000000000 : ℝ)^133 ≤ (48309636340641/100000000000000 : ℝ)^101 := by
    have hnat : (2877568847 : ℕ)^133*100000000000000^101 ≤ 48309636340641^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2877568847 5000000000 48309636340641 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6058479713/10000000000 : ℝ)^133 ≤ (25845180748423/50000000000000 : ℝ)^101 := by
    have hnat : (6058479713 : ℕ)^133*50000000000000^101 ≤ 25845180748423^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6058479713 10000000000 25845180748423 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15019/10000000000 : ℝ), (-2877568847/5000000000 : ℝ), (6058479713/10000000000 : ℝ)] ![(429187/20000000000000 : ℝ), (48309636340641/100000000000000 : ℝ), (25845180748423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15019/10000000000 : ℝ)|^133 ≤ (429187/20000000000000 : ℝ)^101
        have hw : |(-15019/10000000000 : ℝ)|=(15019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2877568847/5000000000 : ℝ)|^133 ≤ (48309636340641/100000000000000 : ℝ)^101
        have hw : |(-2877568847/5000000000 : ℝ)|=(2877568847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6058479713/10000000000 : ℝ)|^133 ≤ (25845180748423/50000000000000 : ℝ)^101
        have hw : |(6058479713/10000000000 : ℝ)|=(6058479713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6843979549/10000000000 : ℝ)*x 0 + (1551324667/5000000000 : ℝ)*x 1 + (676788549/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6843979549/10000000000 : ℝ)^133 ≤ (60691697190999/100000000000000 : ℝ)^101 := by
    have hnat : (6843979549 : ℕ)^133*100000000000000^101 ≤ 60691697190999^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6843979549 10000000000 60691697190999 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551324667/5000000000 : ℝ)^133 ≤ (21413985665273/100000000000000 : ℝ)^101 := by
    have hnat : (1551324667 : ℕ)^133*100000000000000^101 ≤ 21413985665273^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551324667 5000000000 21413985665273 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676788549/2500000000 : ℝ)^133 ≤ (17894317130671/100000000000000 : ℝ)^101 := by
    have hnat : (676788549 : ℕ)^133*100000000000000^101 ≤ 17894317130671^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676788549 2500000000 17894317130671 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6843979549/10000000000 : ℝ), (1551324667/5000000000 : ℝ), (676788549/2500000000 : ℝ)] ![(60691697190999/100000000000000 : ℝ), (21413985665273/100000000000000 : ℝ), (17894317130671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6843979549/10000000000 : ℝ)|^133 ≤ (60691697190999/100000000000000 : ℝ)^101
        have hw : |(6843979549/10000000000 : ℝ)|=(6843979549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551324667/5000000000 : ℝ)|^133 ≤ (21413985665273/100000000000000 : ℝ)^101
        have hw : |(1551324667/5000000000 : ℝ)|=(1551324667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676788549/2500000000 : ℝ)|^133 ≤ (17894317130671/100000000000000 : ℝ)^101
        have hw : |(676788549/2500000000 : ℝ)|=(676788549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3220574851/5000000000 : ℝ)*x 0 + (-173863801/500000000 : ℝ)*x 1 + (-177684813/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3220574851/5000000000 : ℝ)^133 ≤ (56032105635439/100000000000000 : ℝ)^101 := by
    have hnat : (3220574851 : ℕ)^133*100000000000000^101 ≤ 56032105635439^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3220574851 5000000000 56032105635439 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173863801/500000000 : ℝ)^133 ≤ (24882224158837/100000000000000 : ℝ)^101 := by
    have hnat : (173863801 : ℕ)^133*100000000000000^101 ≤ 24882224158837^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173863801 500000000 24882224158837 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177684813/625000000 : ℝ)^133 ≤ (2385708772509/12500000000000 : ℝ)^101 := by
    have hnat : (177684813 : ℕ)^133*12500000000000^101 ≤ 2385708772509^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177684813 625000000 2385708772509 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3220574851/5000000000 : ℝ), (-173863801/500000000 : ℝ), (-177684813/625000000 : ℝ)] ![(56032105635439/100000000000000 : ℝ), (24882224158837/100000000000000 : ℝ), (2385708772509/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3220574851/5000000000 : ℝ)|^133 ≤ (56032105635439/100000000000000 : ℝ)^101
        have hw : |(3220574851/5000000000 : ℝ)|=(3220574851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-173863801/500000000 : ℝ)|^133 ≤ (24882224158837/100000000000000 : ℝ)^101
        have hw : |(-173863801/500000000 : ℝ)|=(173863801/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-177684813/625000000 : ℝ)|^133 ≤ (2385708772509/12500000000000 : ℝ)^101
        have hw : |(-177684813/625000000 : ℝ)|=(177684813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (663969939/2000000000 : ℝ)*x 0 + (-1315679961/5000000000 : ℝ)*x 1 + (3364512361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663969939/2000000000 : ℝ)^133 ≤ (23409576937251/100000000000000 : ℝ)^101 := by
    have hnat : (663969939 : ℕ)^133*100000000000000^101 ≤ 23409576937251^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663969939 2000000000 23409576937251 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315679961/5000000000 : ℝ)^133 ≤ (17237528220291/100000000000000 : ℝ)^101 := by
    have hnat : (1315679961 : ℕ)^133*100000000000000^101 ≤ 17237528220291^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315679961 5000000000 17237528220291 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3364512361/5000000000 : ℝ)^133 ≤ (1483822370623/2500000000000 : ℝ)^101 := by
    have hnat : (3364512361 : ℕ)^133*2500000000000^101 ≤ 1483822370623^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3364512361 5000000000 1483822370623 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663969939/2000000000 : ℝ), (-1315679961/5000000000 : ℝ), (3364512361/5000000000 : ℝ)] ![(23409576937251/100000000000000 : ℝ), (17237528220291/100000000000000 : ℝ), (1483822370623/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663969939/2000000000 : ℝ)|^133 ≤ (23409576937251/100000000000000 : ℝ)^101
        have hw : |(663969939/2000000000 : ℝ)|=(663969939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1315679961/5000000000 : ℝ)|^133 ≤ (17237528220291/100000000000000 : ℝ)^101
        have hw : |(-1315679961/5000000000 : ℝ)|=(1315679961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3364512361/5000000000 : ℝ)|^133 ≤ (1483822370623/2500000000000 : ℝ)^101
        have hw : |(3364512361/5000000000 : ℝ)|=(3364512361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (167973/5000000000 : ℝ)*x 0 + (-1327419769/2000000000 : ℝ)*x 1 + (5147896283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167973/5000000000 : ℝ)^133 ≤ (128484253/100000000000000 : ℝ)^101 := by
    have hnat : (167973 : ℕ)^133*100000000000000^101 ≤ 128484253^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167973 5000000000 128484253 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1327419769/2000000000 : ℝ)^133 ≤ (58287491633281/100000000000000 : ℝ)^101 := by
    have hnat : (1327419769 : ℕ)^133*100000000000000^101 ≤ 58287491633281^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327419769 2000000000 58287491633281 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5147896283/10000000000 : ℝ)^133 ≤ (20856189933069/50000000000000 : ℝ)^101 := by
    have hnat : (5147896283 : ℕ)^133*50000000000000^101 ≤ 20856189933069^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147896283 10000000000 20856189933069 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167973/5000000000 : ℝ), (-1327419769/2000000000 : ℝ), (5147896283/10000000000 : ℝ)] ![(128484253/100000000000000 : ℝ), (58287491633281/100000000000000 : ℝ), (20856189933069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167973/5000000000 : ℝ)|^133 ≤ (128484253/100000000000000 : ℝ)^101
        have hw : |(167973/5000000000 : ℝ)|=(167973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1327419769/2000000000 : ℝ)|^133 ≤ (58287491633281/100000000000000 : ℝ)^101
        have hw : |(-1327419769/2000000000 : ℝ)|=(1327419769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5147896283/10000000000 : ℝ)|^133 ≤ (20856189933069/50000000000000 : ℝ)^101
        have hw : |(5147896283/10000000000 : ℝ)|=(5147896283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3422165213/5000000000 : ℝ)*x 0 + (607254929/2000000000 : ℝ)*x 1 + (2775480893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3422165213/5000000000 : ℝ)^133 ≤ (60695794599599/100000000000000 : ℝ)^101 := by
    have hnat : (3422165213 : ℕ)^133*100000000000000^101 ≤ 60695794599599^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3422165213 5000000000 60695794599599 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (607254929/2000000000 : ℝ)^133 ≤ (20812789769363/100000000000000 : ℝ)^101 := by
    have hnat : (607254929 : ℕ)^133*100000000000000^101 ≤ 20812789769363^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607254929 2000000000 20812789769363 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2775480893/10000000000 : ℝ)^133 ≤ (4622853905597/25000000000000 : ℝ)^101 := by
    have hnat : (2775480893 : ℕ)^133*25000000000000^101 ≤ 4622853905597^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775480893 10000000000 4622853905597 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3422165213/5000000000 : ℝ), (607254929/2000000000 : ℝ), (2775480893/10000000000 : ℝ)] ![(60695794599599/100000000000000 : ℝ), (20812789769363/100000000000000 : ℝ), (4622853905597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3422165213/5000000000 : ℝ)|^133 ≤ (60695794599599/100000000000000 : ℝ)^101
        have hw : |(3422165213/5000000000 : ℝ)|=(3422165213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(607254929/2000000000 : ℝ)|^133 ≤ (20812789769363/100000000000000 : ℝ)^101
        have hw : |(607254929/2000000000 : ℝ)|=(607254929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2775480893/10000000000 : ℝ)|^133 ≤ (4622853905597/25000000000000 : ℝ)^101
        have hw : |(2775480893/10000000000 : ℝ)|=(2775480893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5666618397/10000000000 : ℝ)*x 0 + (-1927273719/5000000000 : ℝ)*x 1 + (-1700692469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5666618397/10000000000 : ℝ)^133 ≤ (47333561658011/100000000000000 : ℝ)^101 := by
    have hnat : (5666618397 : ℕ)^133*100000000000000^101 ≤ 47333561658011^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5666618397 10000000000 47333561658011 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927273719/5000000000 : ℝ)^133 ≤ (28496836375317/100000000000000 : ℝ)^101 := by
    have hnat : (1927273719 : ℕ)^133*100000000000000^101 ≤ 28496836375317^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927273719 5000000000 28496836375317 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1700692469/5000000000 : ℝ)^133 ≤ (12084800974991/50000000000000 : ℝ)^101 := by
    have hnat : (1700692469 : ℕ)^133*50000000000000^101 ≤ 12084800974991^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700692469 5000000000 12084800974991 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5666618397/10000000000 : ℝ), (-1927273719/5000000000 : ℝ), (-1700692469/5000000000 : ℝ)] ![(47333561658011/100000000000000 : ℝ), (28496836375317/100000000000000 : ℝ), (12084800974991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5666618397/10000000000 : ℝ)|^133 ≤ (47333561658011/100000000000000 : ℝ)^101
        have hw : |(5666618397/10000000000 : ℝ)|=(5666618397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927273719/5000000000 : ℝ)|^133 ≤ (28496836375317/100000000000000 : ℝ)^101
        have hw : |(-1927273719/5000000000 : ℝ)|=(1927273719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1700692469/5000000000 : ℝ)|^133 ≤ (12084800974991/50000000000000 : ℝ)^101
        have hw : |(-1700692469/5000000000 : ℝ)|=(1700692469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304086_s4_s4_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2447409409/5000000000 : ℝ)*x 0 + (-2826184937/10000000000 : ℝ)*x 1 + (258877873/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2447409409/5000000000 : ℝ)^133 ≤ (19516653726779/50000000000000 : ℝ)^101 := by
    have hnat : (2447409409 : ℕ)^133*50000000000000^101 ≤ 19516653726779^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2447409409 5000000000 19516653726779 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2826184937/10000000000 : ℝ)^133 ≤ (18937538665543/100000000000000 : ℝ)^101 := by
    have hnat : (2826184937 : ℕ)^133*100000000000000^101 ≤ 18937538665543^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2826184937 10000000000 18937538665543 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258877873/500000000 : ℝ)^133 ≤ (21014576935819/50000000000000 : ℝ)^101 := by
    have hnat : (258877873 : ℕ)^133*50000000000000^101 ≤ 21014576935819^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258877873 500000000 21014576935819 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2447409409/5000000000 : ℝ), (-2826184937/10000000000 : ℝ), (258877873/500000000 : ℝ)] ![(19516653726779/50000000000000 : ℝ), (18937538665543/100000000000000 : ℝ), (21014576935819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2447409409/5000000000 : ℝ)|^133 ≤ (19516653726779/50000000000000 : ℝ)^101
        have hw : |(2447409409/5000000000 : ℝ)|=(2447409409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2826184937/10000000000 : ℝ)|^133 ≤ (18937538665543/100000000000000 : ℝ)^101
        have hw : |(-2826184937/10000000000 : ℝ)|=(2826184937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258877873/500000000 : ℝ)|^133 ≤ (21014576935819/50000000000000 : ℝ)^101
        have hw : |(258877873/500000000 : ℝ)|=(258877873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304086_s4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((28809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7881/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7881/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15171/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15171/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6527/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6527/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-28011/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-28011/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23613/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23613/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (28809/50000 : ℝ) ^ (33/8 : ℝ) ≤ (10287325686785589319/100000000000000000000 : ℝ) := by
    have hpowers : (28809/50000 : ℝ)^33 ≤ (10287325686785589319/100000000000000000000 : ℝ)^8 := by
      have hnat : (28809 : ℕ)^33*100000000000000000000^8 ≤ 10287325686785589319^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28809 50000 10287325686785589319 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28809/50000 : ℝ)) (X := (10287325686785589319/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner0a : (110287325686785589319/100000000000000000000 : ℝ) ≤ (10240218837289313/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (110287325686785589319/100000000000000000000 : ℝ)^8 ≤ (10240218837289313/10000000000000000 : ℝ)^33 := by
      have hnat : (110287325686785589319 : ℕ)^8*10000000000000000^33 ≤ 10240218837289313^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110287325686785589319 100000000000000000000 10240218837289313 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10240218837289313/10000000000000000 : ℝ)) (X := (110287325686785589319/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner0b : (60287325686785589319/50000000000000000000 : ℝ) ≤ (10464016790607983/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (60287325686785589319/50000000000000000000 : ℝ)^8 ≤ (10464016790607983/10000000000000000 : ℝ)^33 := by
      have hnat : (60287325686785589319 : ℕ)^8*10000000000000000^33 ≤ 10464016790607983^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60287325686785589319 50000000000000000000 10464016790607983 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10464016790607983/10000000000000000 : ℝ)) (X := (60287325686785589319/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(240218837289313/5761800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2486643925763/64020000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (28809/50000 : ℝ)) (alpha := (240218837289313/5761800000000000 : ℝ)) (beta := (2486643925763/64020000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (28809/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(240218837289313/5761800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2486643925763/64020000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (7881/10000 : ℝ) ^ (33/8 : ℝ) ≤ (18722678521644996561/50000000000000000000 : ℝ) := by
    have hpowers : (7881/10000 : ℝ)^33 ≤ (18722678521644996561/50000000000000000000 : ℝ)^8 := by
      have hnat : (7881 : ℕ)^33*50000000000000000000^8 ≤ 18722678521644996561^8*10000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7881 10000 18722678521644996561 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7881/10000 : ℝ)) (X := (18722678521644996561/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner1a : (68722678521644996561/50000000000000000000 : ℝ) ≤ (10801549954736599/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (68722678521644996561/50000000000000000000 : ℝ)^8 ≤ (10801549954736599/10000000000000000 : ℝ)^33 := by
      have hnat : (68722678521644996561 : ℕ)^8*10000000000000000^33 ≤ 10801549954736599^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68722678521644996561 50000000000000000000 10801549954736599 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10801549954736599/10000000000000000 : ℝ)) (X := (68722678521644996561/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner1b : (43722678521644996561/25000000000000000000 : ℝ) ≤ (572562037972621/500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (43722678521644996561/25000000000000000000 : ℝ)^8 ≤ (572562037972621/500000000000000 : ℝ)^33 := by
      have hnat : (43722678521644996561 : ℕ)^8*500000000000000^33 ≤ 572562037972621^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43722678521644996561 25000000000000000000 572562037972621 500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (572562037972621/500000000000000 : ℝ)) (X := (43722678521644996561/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(267183318245533/2627000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(649690804715821/7881000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (7881/10000 : ℝ)) (alpha := (267183318245533/2627000000000000 : ℝ)) (beta := (649690804715821/7881000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (7881/10000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(267183318245533/2627000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(649690804715821/7881000000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (15171/20000 : ℝ) ^ (33/8 : ℝ) ≤ (31984154698327291129/100000000000000000000 : ℝ) := by
    have hpowers : (15171/20000 : ℝ)^33 ≤ (31984154698327291129/100000000000000000000 : ℝ)^8 := by
      have hnat : (15171 : ℕ)^33*100000000000000000000^8 ≤ 31984154698327291129^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15171 20000 31984154698327291129 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15171/20000 : ℝ)) (X := (31984154698327291129/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner2a : (131984154698327291129/100000000000000000000 : ℝ) ≤ (427836069973739/400000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (131984154698327291129/100000000000000000000 : ℝ)^8 ≤ (427836069973739/400000000000000 : ℝ)^33 := by
      have hnat : (131984154698327291129 : ℕ)^8*400000000000000^33 ≤ 427836069973739^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131984154698327291129 100000000000000000000 427836069973739 400000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (427836069973739/400000000000000 : ℝ)) (X := (131984154698327291129/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner2b : (81984154698327291129/50000000000000000000 : ℝ) ≤ (56368050506751/50000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (81984154698327291129/50000000000000000000 : ℝ)^8 ≤ (56368050506751/50000000000000 : ℝ)^33 := by
      have hnat : (81984154698327291129 : ℕ)^8*50000000000000^33 ≤ 56368050506751^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81984154698327291129 50000000000000000000 56368050506751 50000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (56368050506751/50000000000000 : ℝ)) (X := (81984154698327291129/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27836069973739/303420000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(23108334080269/303420000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (15171/20000 : ℝ)) (alpha := (27836069973739/303420000000000 : ℝ)) (beta := (23108334080269/303420000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (15171/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27836069973739/303420000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(23108334080269/303420000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-568121673/10000000000 : ℝ)*X 0 0+(-380341563/625000000 : ℝ)*X 0 1+(689872917/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((1461549377/2500000000 : ℝ)*X 2 0+(-182641071/500000000 : ℝ)*X 2 1+(-424668917/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-154239139/10000000000 : ℝ)*X 0 0+(-362239993/500000000 : ℝ)*X 0 1+(2212355993/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((3048150751/5000000000 : ℝ)*X 1 0+(3409418381/10000000000 : ℝ)*X 1 1+(13378323/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((602690753/1000000000 : ℝ)*X 2 0+(-1740701581/5000000000 : ℝ)*X 2 1+(-3355690069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((1477719299/5000000000 : ℝ)*X 0 0+(-1590460877/10000000000 : ℝ)*X 0 1+(1928104737/2500000000 : ℝ)*X 0 2+(1477719299/5000000000 : ℝ)*X 1 0+(-1590460877/10000000000 : ℝ)*X 1 1+(1928104737/2500000000 : ℝ)*X 1 2+(1477719299/5000000000 : ℝ)*X 2 0+(-1590460877/10000000000 : ℝ)*X 2 1+(1928104737/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-15019/10000000000 : ℝ)*X 0 0+(-2877568847/5000000000 : ℝ)*X 0 1+(6058479713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((6843979549/10000000000 : ℝ)*X 1 0+(1551324667/5000000000 : ℝ)*X 1 1+(676788549/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((3220574851/5000000000 : ℝ)*X 2 0+(-173863801/500000000 : ℝ)*X 2 1+(-177684813/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((663969939/2000000000 : ℝ)*X 0 0+(-1315679961/5000000000 : ℝ)*X 0 1+(3364512361/5000000000 : ℝ)*X 0 2+(663969939/2000000000 : ℝ)*X 1 0+(-1315679961/5000000000 : ℝ)*X 1 1+(3364512361/5000000000 : ℝ)*X 1 2+(663969939/2000000000 : ℝ)*X 2 0+(-1315679961/5000000000 : ℝ)*X 2 1+(3364512361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((167973/5000000000 : ℝ)*X 0 0+(-1327419769/2000000000 : ℝ)*X 0 1+(5147896283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((3422165213/5000000000 : ℝ)*X 1 0+(607254929/2000000000 : ℝ)*X 1 1+(2775480893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((5666618397/10000000000 : ℝ)*X 2 0+(-1927273719/5000000000 : ℝ)*X 2 1+(-1700692469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((2447409409/5000000000 : ℝ)*X 0 0+(-2826184937/10000000000 : ℝ)*X 0 1+(258877873/500000000 : ℝ)*X 0 2+(2447409409/5000000000 : ℝ)*X 1 0+(-2826184937/10000000000 : ℝ)*X 1 1+(258877873/500000000 : ℝ)*X 1 2+(2447409409/5000000000 : ℝ)*X 2 0+(-2826184937/10000000000 : ℝ)*X 2 1+(258877873/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304086_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((6527/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6527/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (668619593085027921782232629/88592603206250000000000000000000 : ℝ) := by norm_num
    linear_combination (53779824979/200000000000 : ℝ)*(base40) + (1192881/1000000000000 : ℝ)*(base50) + (3228079/1000000000000 : ℝ)*(base60) + (1640681749809/500000000000 : ℝ)*(major_s4_0) + (1640681749809/500000000000 : ℝ)*(major_s4_1) + (1640681749809/500000000000 : ℝ)*(major_s4_2) + (148507419/500000000000 : ℝ)*(sp_s4_2) + (4399197439893/1000000000000 : ℝ)*(sp_s4_7) + (137477005871/31250000000 : ℝ)*(sp_s4_8) + (219946894083/50000000000 : ℝ)*(sp_s4_9) + (2163433596049/1000000000000 : ℝ)*(sp_s4_13) + (14645687/500000000000 : ℝ)*(sp_s4_16) + (26699601/1000000000000 : ℝ)*(sp_s4_20) + (3337399/50000000000 : ℝ)*(sp_s4_21) + (43269205913/20000000000 : ℝ)*(f.failure) + (137477005871/31250000000 : ℝ)*(f.sum) + (728602758285058959/6642369500000000000000000000000 : ℝ)*base62 + (3216972189173/3160625000000000000000000 : ℝ)*base65 + (265921338793003/1313500000000000000000000000 : ℝ)*base66 + (725480428169/2528500000000000000000000 : ℝ)*base69 + (1234188115243043881/1618745700000000000000000000000 : ℝ)*base71 + (5351992567969/10670000000000000000000000 : ℝ)*base72 + (550848590510087/1313500000000000000000000000 : ℝ)*base74 + (133904216512463/320100000000000000000000000 : ℝ)*base77 + (201072602126371951/1401504500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (67/250000000000000 : ℝ)*base87 + (67/250000000000000 : ℝ)*base89 + (67/250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-28011/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-28011/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4932647193947213575318237/1401504500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2194791/250000000000 : ℝ)*(base21) + (76563/31250000000 : ℝ)*(base33) + (1506107016703/1000000000000 : ℝ)*(base40) + (57980380139/200000000000 : ℝ)*(base60) + (1621274878019/250000000000 : ℝ)*(major_s4_0) + (6485101962091/1000000000000 : ℝ)*(major_s4_1) + (6485101962091/1000000000000 : ℝ)*(major_s4_2) + (11526133/1000000000000 : ℝ)*(sp_s4_13) + (2173615423739/250000000000 : ℝ)*(sp_s4_14) + (1738744724967/200000000000 : ℝ)*(sp_s4_15) + (1086806307353/125000000000 : ℝ)*(sp_s4_16) + (2137864760857/500000000000 : ℝ)*(sp_s4_20) + (22987911/31250000000 : ℝ)*(sp_s4_22) + (534467630981/125000000000 : ℝ)*(f.failure) + (8694461688003/1000000000000 : ℝ)*(f.sum) + (2234969286165360441/13284739000000000000000000000000 : ℝ)*base62 + (1400357163703320767/303420000000000000000000000 : ℝ)*base65 + (9403184983646004497/2627000000000000000000000000 : ℝ)*base66 + (114477617439847/303420000000000000000000000 : ℝ)*base69 + (2217220306951239757/14568711300000000000000000000000 : ℝ)*base70 + (3184274250703/16005000000000000000000000 : ℝ)*base73 + (2823922602035489/7881000000000000000000000000 : ℝ)*base74 + (126553638407813/360112500000000000000000000 : ℝ)*base77 + (5326943556473722903/8409027000000000000000000000000 : ℝ)*base79 + (6953/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (29/1562500000000000 : ℝ)*base87 + (3183/3125000000000000 : ℝ)*base89 + (3183/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23613/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23613/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (477128424546434358924454200677/31893337154250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1405789/250000000000 : ℝ)*(base39) + (858744251379/500000000000 : ℝ)*(base40) + (637347/1000000000000 : ℝ)*(base50) + (1682484097363/250000000000 : ℝ)*(major_s4_0) + (1682484097363/250000000000 : ℝ)*(major_s4_1) + (1682484097363/250000000000 : ℝ)*(major_s4_2) + (23239149/500000000000 : ℝ)*(sp_s4_0) + (131446209/1000000000000 : ℝ)*(sp_s4_2) + (48638071/500000000000 : ℝ)*(sp_s4_7) + (110019109/125000000000 : ℝ)*(sp_s4_15) + (4511279686787/500000000000 : ℝ)*(sp_s4_21) + (4510911487571/500000000000 : ℝ)*(sp_s4_22) + (1804514336361/200000000000 : ℝ)*(sp_s4_23) + (2218582332089/500000000000 : ℝ)*(sp_s4_27) + (2218582332089/500000000000 : ℝ)*(f.failure) + (4511351564007/500000000000 : ℝ)*(f.sum) + (1048176592046577013/3321184750000000000000000000000 : ℝ)*base62 + (4856530694213/75855000000000000000000000 : ℝ)*base65 + (157185249712629/656750000000000000000000000 : ℝ)*base67 + (1369825660639/15171000000000000000000000 : ℝ)*base68 + (810032240371291493/7284355650000000000000000000000 : ℝ)*base71 + (506463216587/1600500000000000000000000 : ℝ)*base73 + (393802956760501/985125000000000000000000000 : ℝ)*base74 + (266043502057639/1440450000000000000000000000 : ℝ)*base77 + (1465590605332333379/2102256750000000000000000000000 : ℝ)*base79 + (351/6250000000000000 : ℝ)*base87 + (351/6250000000000000 : ℝ)*base89 + (351/6250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((28809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(28809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-7881/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7881/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15171/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15171/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6527/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6527/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-28011/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-28011/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23613/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23613/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304086_s4 p hpa hpb X hX hprev3

#print axioms solution

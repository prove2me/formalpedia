-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313053_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:32:51.823198+00:00
-- url     : https://prove2.me/submissions/64ee57ed-6233-458c-a0ba-e82d167f6dc8

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
theorem collision_support_c313053_s2_s2_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209684551/10000000000 : ℝ)*x 0 + (1278387389/2500000000 : ℝ)*x 1 + (2577208611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209684551/10000000000 : ℝ)^37 ≤ (14569876603507/100000000000000 : ℝ)^29 := by
    have hnat : (2209684551 : ℕ)^37*100000000000000^29 ≤ 14569876603507^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209684551 10000000000 14569876603507 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1278387389/2500000000 : ℝ)^37 ≤ (10624538031627/25000000000000 : ℝ)^29 := by
    have hnat : (1278387389 : ℕ)^37*25000000000000^29 ≤ 10624538031627^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278387389 2500000000 10624538031627 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2577208611/5000000000 : ℝ)^37 ≤ (10732992814491/25000000000000 : ℝ)^29 := by
    have hnat : (2577208611 : ℕ)^37*25000000000000^29 ≤ 10732992814491^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577208611 5000000000 10732992814491 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209684551/10000000000 : ℝ), (1278387389/2500000000 : ℝ), (2577208611/5000000000 : ℝ)] ![(14569876603507/100000000000000 : ℝ), (10624538031627/25000000000000 : ℝ), (10732992814491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209684551/10000000000 : ℝ)|^37 ≤ (14569876603507/100000000000000 : ℝ)^29
        have hw : |(-2209684551/10000000000 : ℝ)|=(2209684551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1278387389/2500000000 : ℝ)|^37 ≤ (10624538031627/25000000000000 : ℝ)^29
        have hw : |(1278387389/2500000000 : ℝ)|=(1278387389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2577208611/5000000000 : ℝ)|^37 ≤ (10732992814491/25000000000000 : ℝ)^29
        have hw : |(2577208611/5000000000 : ℝ)|=(2577208611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2251097693/5000000000 : ℝ)*x 0 + (-208526493/1250000000 : ℝ)*x 1 + (3071133511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251097693/5000000000 : ℝ)^37 ≤ (36125782222893/100000000000000 : ℝ)^29 := by
    have hnat : (2251097693 : ℕ)^37*100000000000000^29 ≤ 36125782222893^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251097693 5000000000 36125782222893 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208526493/1250000000 : ℝ)^37 ≤ (2035775278231/20000000000000 : ℝ)^29 := by
    have hnat : (208526493 : ℕ)^37*20000000000000^29 ≤ 2035775278231^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208526493 1250000000 2035775278231 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3071133511/5000000000 : ℝ)^37 ≤ (1342383534147/2500000000000 : ℝ)^29 := by
    have hnat : (3071133511 : ℕ)^37*2500000000000^29 ≤ 1342383534147^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071133511 5000000000 1342383534147 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251097693/5000000000 : ℝ), (-208526493/1250000000 : ℝ), (3071133511/5000000000 : ℝ)] ![(36125782222893/100000000000000 : ℝ), (2035775278231/20000000000000 : ℝ), (1342383534147/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251097693/5000000000 : ℝ)|^37 ≤ (36125782222893/100000000000000 : ℝ)^29
        have hw : |(2251097693/5000000000 : ℝ)|=(2251097693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208526493/1250000000 : ℝ)|^37 ≤ (2035775278231/20000000000000 : ℝ)^29
        have hw : |(-208526493/1250000000 : ℝ)|=(208526493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3071133511/5000000000 : ℝ)|^37 ≤ (1342383534147/2500000000000 : ℝ)^29
        have hw : |(3071133511/5000000000 : ℝ)|=(3071133511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (565681671/1250000000 : ℝ)*x 0 + (767090193/1250000000 : ℝ)*x 1 + (-1645505947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565681671/1250000000 : ℝ)^37 ≤ (2272753547509/6250000000000 : ℝ)^29 := by
    have hnat : (565681671 : ℕ)^37*6250000000000^29 ≤ 2272753547509^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565681671 1250000000 2272753547509 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (767090193/1250000000 : ℝ)^37 ≤ (53633497514131/100000000000000 : ℝ)^29 := by
    have hnat : (767090193 : ℕ)^37*100000000000000^29 ≤ 53633497514131^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767090193 1250000000 53633497514131 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1645505947/10000000000 : ℝ)^37 ≤ (2500611426939/25000000000000 : ℝ)^29 := by
    have hnat : (1645505947 : ℕ)^37*25000000000000^29 ≤ 2500611426939^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645505947 10000000000 2500611426939 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(565681671/1250000000 : ℝ), (767090193/1250000000 : ℝ), (-1645505947/10000000000 : ℝ)] ![(2272753547509/6250000000000 : ℝ), (53633497514131/100000000000000 : ℝ), (2500611426939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(565681671/1250000000 : ℝ)|^37 ≤ (2272753547509/6250000000000 : ℝ)^29
        have hw : |(565681671/1250000000 : ℝ)|=(565681671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(767090193/1250000000 : ℝ)|^37 ≤ (53633497514131/100000000000000 : ℝ)^29
        have hw : |(767090193/1250000000 : ℝ)|=(767090193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1645505947/10000000000 : ℝ)|^37 ≤ (2500611426939/25000000000000 : ℝ)^29
        have hw : |(-1645505947/10000000000 : ℝ)|=(1645505947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-263887329/1250000000 : ℝ)*x 0 + (808487/1953125 : ℝ)*x 1 + (76895647/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263887329/1250000000 : ℝ)^37 ≤ (13745674270501/100000000000000 : ℝ)^29 := by
    have hnat : (263887329 : ℕ)^37*100000000000000^29 ≤ 13745674270501^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263887329 1250000000 13745674270501 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (808487/1953125 : ℝ)^37 ≤ (16227144758919/50000000000000 : ℝ)^29 := by
    have hnat : (808487 : ℕ)^37*50000000000000^29 ≤ 16227144758919^29*1953125^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808487 1953125 16227144758919 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76895647/125000000 : ℝ)^37 ≤ (26900018102711/50000000000000 : ℝ)^29 := by
    have hnat : (76895647 : ℕ)^37*50000000000000^29 ≤ 26900018102711^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76895647 125000000 26900018102711 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263887329/1250000000 : ℝ), (808487/1953125 : ℝ), (76895647/125000000 : ℝ)] ![(13745674270501/100000000000000 : ℝ), (16227144758919/50000000000000 : ℝ), (26900018102711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263887329/1250000000 : ℝ)|^37 ≤ (13745674270501/100000000000000 : ℝ)^29
        have hw : |(-263887329/1250000000 : ℝ)|=(263887329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(808487/1953125 : ℝ)|^37 ≤ (16227144758919/50000000000000 : ℝ)^29
        have hw : |(808487/1953125 : ℝ)|=(808487/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(76895647/125000000 : ℝ)|^37 ≤ (26900018102711/50000000000000 : ℝ)^29
        have hw : |(76895647/125000000 : ℝ)|=(76895647/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2082258039/5000000000 : ℝ)*x 0 + (-10179557/80000000 : ℝ)*x 1 + (3354260557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082258039/5000000000 : ℝ)^37 ≤ (32705201624791/100000000000000 : ℝ)^29 := by
    have hnat : (2082258039 : ℕ)^37*100000000000000^29 ≤ 32705201624791^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082258039 5000000000 32705201624791 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10179557/80000000 : ℝ)^37 ≤ (1441028994963/20000000000000 : ℝ)^29 := by
    have hnat : (10179557 : ℕ)^37*20000000000000^29 ≤ 1441028994963^29*80000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10179557 80000000 1441028994963 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3354260557/5000000000 : ℝ)^37 ≤ (60089653379951/100000000000000 : ℝ)^29 := by
    have hnat : (3354260557 : ℕ)^37*100000000000000^29 ≤ 60089653379951^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3354260557 5000000000 60089653379951 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2082258039/5000000000 : ℝ), (-10179557/80000000 : ℝ), (3354260557/5000000000 : ℝ)] ![(32705201624791/100000000000000 : ℝ), (1441028994963/20000000000000 : ℝ), (60089653379951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2082258039/5000000000 : ℝ)|^37 ≤ (32705201624791/100000000000000 : ℝ)^29
        have hw : |(2082258039/5000000000 : ℝ)|=(2082258039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10179557/80000000 : ℝ)|^37 ≤ (1441028994963/20000000000000 : ℝ)^29
        have hw : |(-10179557/80000000 : ℝ)|=(10179557/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3354260557/5000000000 : ℝ)|^37 ≤ (60089653379951/100000000000000 : ℝ)^29
        have hw : |(3354260557/5000000000 : ℝ)|=(3354260557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (65436879/156250000 : ℝ)*x 0 + (7020950743/10000000000 : ℝ)*x 1 + (-28101797/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65436879/156250000 : ℝ)^37 ≤ (658805762159/2000000000000 : ℝ)^29 := by
    have hnat : (65436879 : ℕ)^37*2000000000000^29 ≤ 658805762159^29*156250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65436879 156250000 658805762159 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7020950743/10000000000 : ℝ)^37 ≤ (6368283495403/10000000000000 : ℝ)^29 := by
    have hnat : (7020950743 : ℕ)^37*10000000000000^29 ≤ 6368283495403^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7020950743 10000000000 6368283495403 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28101797/400000000 : ℝ)^37 ≤ (1688438461437/50000000000000 : ℝ)^29 := by
    have hnat : (28101797 : ℕ)^37*50000000000000^29 ≤ 1688438461437^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28101797 400000000 1688438461437 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65436879/156250000 : ℝ), (7020950743/10000000000 : ℝ), (-28101797/400000000 : ℝ)] ![(658805762159/2000000000000 : ℝ), (6368283495403/10000000000000 : ℝ), (1688438461437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65436879/156250000 : ℝ)|^37 ≤ (658805762159/2000000000000 : ℝ)^29
        have hw : |(65436879/156250000 : ℝ)|=(65436879/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7020950743/10000000000 : ℝ)|^37 ≤ (6368283495403/10000000000000 : ℝ)^29
        have hw : |(7020950743/10000000000 : ℝ)|=(7020950743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28101797/400000000 : ℝ)|^37 ≤ (1688438461437/50000000000000 : ℝ)^29
        have hw : |(-28101797/400000000 : ℝ)|=(28101797/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6551020353/10000000000 : ℝ)*x 0 + (4186120443/10000000000 : ℝ)*x 1 + (1486035051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6551020353/10000000000 : ℝ)^37 ≤ (58295570292441/100000000000000 : ℝ)^29 := by
    have hnat : (6551020353 : ℕ)^37*100000000000000^29 ≤ 58295570292441^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6551020353 10000000000 58295570292441 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4186120443/10000000000 : ℝ)^37 ≤ (3292182622761/10000000000000 : ℝ)^29 := by
    have hnat : (4186120443 : ℕ)^37*10000000000000^29 ≤ 3292182622761^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186120443 10000000000 3292182622761 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1486035051/10000000000 : ℝ)^37 ≤ (878260346537/10000000000000 : ℝ)^29 := by
    have hnat : (1486035051 : ℕ)^37*10000000000000^29 ≤ 878260346537^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486035051 10000000000 878260346537 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6551020353/10000000000 : ℝ), (4186120443/10000000000 : ℝ), (1486035051/10000000000 : ℝ)] ![(58295570292441/100000000000000 : ℝ), (3292182622761/10000000000000 : ℝ), (878260346537/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6551020353/10000000000 : ℝ)|^37 ≤ (58295570292441/100000000000000 : ℝ)^29
        have hw : |(6551020353/10000000000 : ℝ)|=(6551020353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4186120443/10000000000 : ℝ)|^37 ≤ (3292182622761/10000000000000 : ℝ)^29
        have hw : |(4186120443/10000000000 : ℝ)|=(4186120443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1486035051/10000000000 : ℝ)|^37 ≤ (878260346537/10000000000000 : ℝ)^29
        have hw : |(1486035051/10000000000 : ℝ)|=(1486035051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-9481759/78125000 : ℝ)*x 0 + (4904987387/10000000000 : ℝ)*x 1 + (759052781/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9481759/78125000 : ℝ)^37 ≤ (1356645880941/20000000000000 : ℝ)^29 := by
    have hnat : (9481759 : ℕ)^37*20000000000000^29 ≤ 1356645880941^29*78125000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9481759 78125000 1356645880941 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4904987387/10000000000 : ℝ)^37 ≤ (10074804634037/25000000000000 : ℝ)^29 := by
    have hnat : (4904987387 : ℕ)^37*25000000000000^29 ≤ 10074804634037^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4904987387 10000000000 10074804634037 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (759052781/1250000000 : ℝ)^37 ≤ (1653673501321/3125000000000 : ℝ)^29 := by
    have hnat : (759052781 : ℕ)^37*3125000000000^29 ≤ 1653673501321^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759052781 1250000000 1653673501321 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9481759/78125000 : ℝ), (4904987387/10000000000 : ℝ), (759052781/1250000000 : ℝ)] ![(1356645880941/20000000000000 : ℝ), (10074804634037/25000000000000 : ℝ), (1653673501321/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9481759/78125000 : ℝ)|^37 ≤ (1356645880941/20000000000000 : ℝ)^29
        have hw : |(-9481759/78125000 : ℝ)|=(9481759/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4904987387/10000000000 : ℝ)|^37 ≤ (10074804634037/25000000000000 : ℝ)^29
        have hw : |(4904987387/10000000000 : ℝ)|=(4904987387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(759052781/1250000000 : ℝ)|^37 ≤ (1653673501321/3125000000000 : ℝ)^29
        have hw : |(759052781/1250000000 : ℝ)|=(759052781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1021760221/2500000000 : ℝ)*x 0 + (-1339890719/10000000000 : ℝ)*x 1 + (3366657703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021760221/2500000000 : ℝ)^37 ≤ (31930922077099/100000000000000 : ℝ)^29 := by
    have hnat : (1021760221 : ℕ)^37*100000000000000^29 ≤ 31930922077099^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021760221 2500000000 31930922077099 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1339890719/10000000000 : ℝ)^37 ≤ (7695926861403/100000000000000 : ℝ)^29 := by
    have hnat : (1339890719 : ℕ)^37*100000000000000^29 ≤ 7695926861403^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339890719 10000000000 7695926861403 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3366657703/5000000000 : ℝ)^37 ≤ (30186575523317/50000000000000 : ℝ)^29 := by
    have hnat : (3366657703 : ℕ)^37*50000000000000^29 ≤ 30186575523317^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3366657703 5000000000 30186575523317 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1021760221/2500000000 : ℝ), (-1339890719/10000000000 : ℝ), (3366657703/5000000000 : ℝ)] ![(31930922077099/100000000000000 : ℝ), (7695926861403/100000000000000 : ℝ), (30186575523317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1021760221/2500000000 : ℝ)|^37 ≤ (31930922077099/100000000000000 : ℝ)^29
        have hw : |(1021760221/2500000000 : ℝ)|=(1021760221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1339890719/10000000000 : ℝ)|^37 ≤ (7695926861403/100000000000000 : ℝ)^29
        have hw : |(-1339890719/10000000000 : ℝ)|=(1339890719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3366657703/5000000000 : ℝ)|^37 ≤ (30186575523317/50000000000000 : ℝ)^29
        have hw : |(3366657703/5000000000 : ℝ)|=(3366657703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5575229211/10000000000 : ℝ)*x 0 + (5687570139/10000000000 : ℝ)*x 1 + (-781772001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5575229211/10000000000 : ℝ)^37 ≤ (47453280148251/100000000000000 : ℝ)^29 := by
    have hnat : (5575229211 : ℕ)^37*100000000000000^29 ≤ 47453280148251^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5575229211 10000000000 47453280148251 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5687570139/10000000000 : ℝ)^37 ≤ (9735322693979/20000000000000 : ℝ)^29 := by
    have hnat : (5687570139 : ℕ)^37*20000000000000^29 ≤ 9735322693979^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687570139 10000000000 9735322693979 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (781772001/10000000000 : ℝ)^37 ≤ (967526592507/25000000000000 : ℝ)^29 := by
    have hnat : (781772001 : ℕ)^37*25000000000000^29 ≤ 967526592507^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781772001 10000000000 967526592507 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5575229211/10000000000 : ℝ), (5687570139/10000000000 : ℝ), (-781772001/10000000000 : ℝ)] ![(47453280148251/100000000000000 : ℝ), (9735322693979/20000000000000 : ℝ), (967526592507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5575229211/10000000000 : ℝ)|^37 ≤ (47453280148251/100000000000000 : ℝ)^29
        have hw : |(5575229211/10000000000 : ℝ)|=(5575229211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5687570139/10000000000 : ℝ)|^37 ≤ (9735322693979/20000000000000 : ℝ)^29
        have hw : |(5687570139/10000000000 : ℝ)|=(5687570139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-781772001/10000000000 : ℝ)|^37 ≤ (967526592507/25000000000000 : ℝ)^29
        have hw : |(-781772001/10000000000 : ℝ)|=(781772001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (494171323/625000000 : ℝ)*x 0 + (639306313/2500000000 : ℝ)*x 1 + (1426782727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (494171323/625000000 : ℝ)^37 ≤ (37053472274873/50000000000000 : ℝ)^29 := by
    have hnat : (494171323 : ℕ)^37*50000000000000^29 ≤ 37053472274873^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494171323 625000000 37053472274873 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639306313/2500000000 : ℝ)^37 ≤ (17554760593021/100000000000000 : ℝ)^29 := by
    have hnat : (639306313 : ℕ)^37*100000000000000^29 ≤ 17554760593021^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639306313 2500000000 17554760593021 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1426782727/10000000000 : ℝ)^37 ≤ (416914742367/5000000000000 : ℝ)^29 := by
    have hnat : (1426782727 : ℕ)^37*5000000000000^29 ≤ 416914742367^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426782727 10000000000 416914742367 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(494171323/625000000 : ℝ), (639306313/2500000000 : ℝ), (1426782727/10000000000 : ℝ)] ![(37053472274873/50000000000000 : ℝ), (17554760593021/100000000000000 : ℝ), (416914742367/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(494171323/625000000 : ℝ)|^37 ≤ (37053472274873/50000000000000 : ℝ)^29
        have hw : |(494171323/625000000 : ℝ)|=(494171323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(639306313/2500000000 : ℝ)|^37 ≤ (17554760593021/100000000000000 : ℝ)^29
        have hw : |(639306313/2500000000 : ℝ)|=(639306313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1426782727/10000000000 : ℝ)|^37 ≤ (416914742367/5000000000000 : ℝ)^29
        have hw : |(1426782727/10000000000 : ℝ)|=(1426782727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-287670283/2500000000 : ℝ)*x 0 + (5638750709/10000000000 : ℝ)*x 1 + (5396262497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287670283/2500000000 : ℝ)^37 ≤ (3168677919029/50000000000000 : ℝ)^29 := by
    have hnat : (287670283 : ℕ)^37*50000000000000^29 ≤ 3168677919029^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287670283 2500000000 3168677919029 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5638750709/10000000000 : ℝ)^37 ≤ (48144168817733/100000000000000 : ℝ)^29 := by
    have hnat : (5638750709 : ℕ)^37*100000000000000^29 ≤ 48144168817733^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5638750709 10000000000 48144168817733 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396262497/10000000000 : ℝ)^37 ≤ (711226177129/1562500000000 : ℝ)^29 := by
    have hnat : (5396262497 : ℕ)^37*1562500000000^29 ≤ 711226177129^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396262497 10000000000 711226177129 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-287670283/2500000000 : ℝ), (5638750709/10000000000 : ℝ), (5396262497/10000000000 : ℝ)] ![(3168677919029/50000000000000 : ℝ), (48144168817733/100000000000000 : ℝ), (711226177129/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-287670283/2500000000 : ℝ)|^37 ≤ (3168677919029/50000000000000 : ℝ)^29
        have hw : |(-287670283/2500000000 : ℝ)|=(287670283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5638750709/10000000000 : ℝ)|^37 ≤ (48144168817733/100000000000000 : ℝ)^29
        have hw : |(5638750709/10000000000 : ℝ)|=(5638750709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396262497/10000000000 : ℝ)|^37 ≤ (711226177129/1562500000000 : ℝ)^29
        have hw : |(5396262497/10000000000 : ℝ)|=(5396262497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5614768291/10000000000 : ℝ)*x 0 + (-865690599/10000000000 : ℝ)*x 1 + (5598775981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5614768291/10000000000 : ℝ)^37 ≤ (23941535758743/50000000000000 : ℝ)^29 := by
    have hnat : (5614768291 : ℕ)^37*50000000000000^29 ≤ 23941535758743^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614768291 10000000000 23941535758743 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (865690599/10000000000 : ℝ)^37 ≤ (881558978901/20000000000000 : ℝ)^29 := by
    have hnat : (865690599 : ℕ)^37*20000000000000^29 ≤ 881558978901^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865690599 10000000000 881558978901 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5598775981/10000000000 : ℝ)^37 ≤ (11927283394711/25000000000000 : ℝ)^29 := by
    have hnat : (5598775981 : ℕ)^37*25000000000000^29 ≤ 11927283394711^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598775981 10000000000 11927283394711 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5614768291/10000000000 : ℝ), (-865690599/10000000000 : ℝ), (5598775981/10000000000 : ℝ)] ![(23941535758743/50000000000000 : ℝ), (881558978901/20000000000000 : ℝ), (11927283394711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5614768291/10000000000 : ℝ)|^37 ≤ (23941535758743/50000000000000 : ℝ)^29
        have hw : |(5614768291/10000000000 : ℝ)|=(5614768291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-865690599/10000000000 : ℝ)|^37 ≤ (881558978901/20000000000000 : ℝ)^29
        have hw : |(-865690599/10000000000 : ℝ)|=(865690599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5598775981/10000000000 : ℝ)|^37 ≤ (11927283394711/25000000000000 : ℝ)^29
        have hw : |(5598775981/10000000000 : ℝ)|=(5598775981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2021878041/5000000000 : ℝ)*x 0 + (1375186509/2000000000 : ℝ)*x 1 + (-1172419299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021878041/5000000000 : ℝ)^37 ≤ (3150009287781/10000000000000 : ℝ)^29 := by
    have hnat : (2021878041 : ℕ)^37*10000000000000^29 ≤ 3150009287781^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021878041 5000000000 3150009287781 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375186509/2000000000 : ℝ)^37 ≤ (7751175696103/12500000000000 : ℝ)^29 := by
    have hnat : (1375186509 : ℕ)^37*12500000000000^29 ≤ 7751175696103^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375186509 2000000000 7751175696103 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1172419299/10000000000 : ℝ)^37 ≤ (3245250772393/50000000000000 : ℝ)^29 := by
    have hnat : (1172419299 : ℕ)^37*50000000000000^29 ≤ 3245250772393^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1172419299 10000000000 3245250772393 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2021878041/5000000000 : ℝ), (1375186509/2000000000 : ℝ), (-1172419299/10000000000 : ℝ)] ![(3150009287781/10000000000000 : ℝ), (7751175696103/12500000000000 : ℝ), (3245250772393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2021878041/5000000000 : ℝ)|^37 ≤ (3150009287781/10000000000000 : ℝ)^29
        have hw : |(2021878041/5000000000 : ℝ)|=(2021878041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375186509/2000000000 : ℝ)|^37 ≤ (7751175696103/12500000000000 : ℝ)^29
        have hw : |(1375186509/2000000000 : ℝ)|=(1375186509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1172419299/10000000000 : ℝ)|^37 ≤ (3245250772393/50000000000000 : ℝ)^29
        have hw : |(-1172419299/10000000000 : ℝ)|=(1172419299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313053_s2_s2_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1008276049/1250000000 : ℝ)*x 0 + (960891893/5000000000 : ℝ)*x 1 + (116973927/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008276049/1250000000 : ℝ)^37 ≤ (19004790417/25000000000 : ℝ)^29 := by
    have hnat : (1008276049 : ℕ)^37*25000000000^29 ≤ 19004790417^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008276049 1250000000 19004790417 25000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960891893/5000000000 : ℝ)^37 ≤ (3048216305463/25000000000000 : ℝ)^29 := by
    have hnat : (960891893 : ℕ)^37*25000000000000^29 ≤ 3048216305463^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960891893 5000000000 3048216305463 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116973927/625000000 : ℝ)^37 ≤ (11787973104283/100000000000000 : ℝ)^29 := by
    have hnat : (116973927 : ℕ)^37*100000000000000^29 ≤ 11787973104283^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116973927 625000000 11787973104283 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1008276049/1250000000 : ℝ), (960891893/5000000000 : ℝ), (116973927/625000000 : ℝ)] ![(19004790417/25000000000 : ℝ), (3048216305463/25000000000000 : ℝ), (11787973104283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1008276049/1250000000 : ℝ)|^37 ≤ (19004790417/25000000000 : ℝ)^29
        have hw : |(1008276049/1250000000 : ℝ)|=(1008276049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(960891893/5000000000 : ℝ)|^37 ≤ (3048216305463/25000000000000 : ℝ)^29
        have hw : |(960891893/5000000000 : ℝ)|=(960891893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(116973927/625000000 : ℝ)|^37 ≤ (11787973104283/100000000000000 : ℝ)^29
        have hw : |(116973927/625000000 : ℝ)|=(116973927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313053_s2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((12193/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12193/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6553/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6553/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32043/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32043/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((34399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(807/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(807/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7739/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7739/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (12193/20000 : ℝ) ^ (73/16 : ℝ) ≤ (10457554527654331209/100000000000000000000 : ℝ) := by
    have hpowers : (12193/20000 : ℝ)^73 ≤ (10457554527654331209/100000000000000000000 : ℝ)^16 := by
      have hnat : (12193 : ℕ)^73*100000000000000000000^16 ≤ 10457554527654331209^16*20000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12193 20000 10457554527654331209 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12193/20000 : ℝ)) (X := (10457554527654331209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (110457554527654331209/100000000000000000000 : ℝ) ≤ (10220390513383307/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (110457554527654331209/100000000000000000000 : ℝ)^16 ≤ (10220390513383307/10000000000000000 : ℝ)^73 := by
      have hnat : (110457554527654331209 : ℕ)^16*10000000000000000^73 ≤ 10220390513383307^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110457554527654331209 100000000000000000000 10220390513383307 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10220390513383307/10000000000000000 : ℝ)) (X := (110457554527654331209/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (60457554527654331209/50000000000000000000 : ℝ) ≤ (260626122164007/250000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (60457554527654331209/50000000000000000000 : ℝ)^16 ≤ (260626122164007/250000000000000 : ℝ)^73 := by
      have hnat : (60457554527654331209 : ℕ)^16*250000000000000^73 ≤ 260626122164007^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60457554527654331209 50000000000000000000 260626122164007 250000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (260626122164007/250000000000000 : ℝ)) (X := (60457554527654331209/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(220390513383307/6096500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(204654373176973/6096500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (12193/20000 : ℝ)) (alpha := (220390513383307/6096500000000000 : ℝ)) (beta := (204654373176973/6096500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (12193/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(220390513383307/6096500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(204654373176973/6096500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (6553/10000 : ℝ) ^ (73/16 : ℝ) ≤ (7269060284989255331/50000000000000000000 : ℝ) := by
    have hpowers : (6553/10000 : ℝ)^73 ≤ (7269060284989255331/50000000000000000000 : ℝ)^16 := by
      have hnat : (6553 : ℕ)^73*50000000000000000000^16 ≤ 7269060284989255331^16*10000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6553 10000 7269060284989255331 50000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6553/10000 : ℝ)) (X := (7269060284989255331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (57269060284989255331/50000000000000000000 : ℝ) ≤ (2060395321839601/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (57269060284989255331/50000000000000000000 : ℝ)^16 ≤ (2060395321839601/2000000000000000 : ℝ)^73 := by
      have hnat : (57269060284989255331 : ℕ)^16*2000000000000000^73 ≤ 2060395321839601^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57269060284989255331 50000000000000000000 2060395321839601 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2060395321839601/2000000000000000 : ℝ)) (X := (57269060284989255331/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (32269060284989255331/25000000000000000000 : ℝ) ≤ (528767904173587/500000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (32269060284989255331/25000000000000000000 : ℝ)^16 ≤ (528767904173587/500000000000000 : ℝ)^73 := by
      have hnat : (32269060284989255331 : ℕ)^16*500000000000000^73 ≤ 528767904173587^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32269060284989255331 25000000000000000000 528767904173587 500000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (528767904173587/500000000000000 : ℝ)) (X := (32269060284989255331/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(60395321839601/1310600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(54676294854747/1310600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (6553/10000 : ℝ)) (alpha := (60395321839601/1310600000000000 : ℝ)) (beta := (54676294854747/1310600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6553/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(60395321839601/1310600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(54676294854747/1310600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (32043/50000 : ℝ) ^ (73/16 : ℝ) ≤ (13132788265349545783/100000000000000000000 : ℝ) := by
    have hpowers : (32043/50000 : ℝ)^73 ≤ (13132788265349545783/100000000000000000000 : ℝ)^16 := by
      have hnat : (32043 : ℕ)^73*100000000000000000000^16 ≤ 13132788265349545783^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32043 50000 13132788265349545783 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32043/50000 : ℝ)) (X := (13132788265349545783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (113132788265349545783/100000000000000000000 : ℝ) ≤ (10274138659484567/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (113132788265349545783/100000000000000000000 : ℝ)^16 ≤ (10274138659484567/10000000000000000 : ℝ)^73 := by
      have hnat : (113132788265349545783 : ℕ)^16*10000000000000000^73 ≤ 10274138659484567^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113132788265349545783 100000000000000000000 10274138659484567 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10274138659484567/10000000000000000 : ℝ)) (X := (113132788265349545783/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (63132788265349545783/50000000000000000000 : ℝ) ≤ (10524450858517079/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (63132788265349545783/50000000000000000000 : ℝ)^16 ≤ (10524450858517079/10000000000000000 : ℝ)^73 := by
      have hnat : (63132788265349545783 : ℕ)^16*10000000000000000^73 ≤ 10524450858517079^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63132788265349545783 50000000000000000000 10524450858517079 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10524450858517079/10000000000000000 : ℝ)) (X := (63132788265349545783/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(274138659484567/6408600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1303709369961/33378125000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (32043/50000 : ℝ)) (alpha := (274138659484567/6408600000000000 : ℝ)) (beta := (1303709369961/33378125000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (32043/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(274138659484567/6408600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1303709369961/33378125000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2209684551/10000000000 : ℝ)*X 0 0+(1278387389/2500000000 : ℝ)*X 0 1+(2577208611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2251097693/5000000000 : ℝ)*X 1 0+(-208526493/1250000000 : ℝ)*X 1 1+(3071133511/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((565681671/1250000000 : ℝ)*X 2 0+(767090193/1250000000 : ℝ)*X 2 1+(-1645505947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-263887329/1250000000 : ℝ)*X 0 0+(808487/1953125 : ℝ)*X 0 1+(76895647/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2082258039/5000000000 : ℝ)*X 1 0+(-10179557/80000000 : ℝ)*X 1 1+(3354260557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((65436879/156250000 : ℝ)*X 2 0+(7020950743/10000000000 : ℝ)*X 2 1+(-28101797/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((6551020353/10000000000 : ℝ)*X 0 0+(4186120443/10000000000 : ℝ)*X 0 1+(1486035051/10000000000 : ℝ)*X 0 2+(6551020353/10000000000 : ℝ)*X 1 0+(4186120443/10000000000 : ℝ)*X 1 1+(1486035051/10000000000 : ℝ)*X 1 2+(6551020353/10000000000 : ℝ)*X 2 0+(4186120443/10000000000 : ℝ)*X 2 1+(1486035051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-9481759/78125000 : ℝ)*X 0 0+(4904987387/10000000000 : ℝ)*X 0 1+(759052781/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1021760221/2500000000 : ℝ)*X 1 0+(-1339890719/10000000000 : ℝ)*X 1 1+(3366657703/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5575229211/10000000000 : ℝ)*X 2 0+(5687570139/10000000000 : ℝ)*X 2 1+(-781772001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((494171323/625000000 : ℝ)*X 0 0+(639306313/2500000000 : ℝ)*X 0 1+(1426782727/10000000000 : ℝ)*X 0 2+(494171323/625000000 : ℝ)*X 1 0+(639306313/2500000000 : ℝ)*X 1 1+(1426782727/10000000000 : ℝ)*X 1 2+(494171323/625000000 : ℝ)*X 2 0+(639306313/2500000000 : ℝ)*X 2 1+(1426782727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-287670283/2500000000 : ℝ)*X 0 0+(5638750709/10000000000 : ℝ)*X 0 1+(5396262497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5614768291/10000000000 : ℝ)*X 1 0+(-865690599/10000000000 : ℝ)*X 1 1+(5598775981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2021878041/5000000000 : ℝ)*X 2 0+(1375186509/2000000000 : ℝ)*X 2 1+(-1172419299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1008276049/1250000000 : ℝ)*X 0 0+(960891893/5000000000 : ℝ)*X 0 1+(116973927/625000000 : ℝ)*X 0 2+(1008276049/1250000000 : ℝ)*X 1 0+(960891893/5000000000 : ℝ)*X 1 1+(116973927/625000000 : ℝ)*X 1 2+(1008276049/1250000000 : ℝ)*X 2 0+(960891893/5000000000 : ℝ)*X 2 1+(116973927/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313053_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((34399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (389859663221005804823259988931/85341968644900000000000000000000000 : ℝ) := by norm_num
    linear_combination (109223/500000000000 : ℝ)*(base5) + (33391/200000000000 : ℝ)*(base8) + (16091266351/1000000000000 : ℝ)*(base49) + (40559508147/62500000000 : ℝ)*(base59) + (4980578404469/1000000000000 : ℝ)*(major_s2_0) + (4980578404469/1000000000000 : ℝ)*(major_s2_1) + (4980578404469/1000000000000 : ℝ)*(major_s2_2) + (36243731/1000000000000 : ℝ)*(sp_s2_0) + (280899966229/40000000000 : ℝ)*(sp_s2_7) + (7022431161101/1000000000000 : ℝ)*(sp_s2_8) + (3511222330687/500000000000 : ℝ)*(sp_s2_9) + (1469309750669/500000000000 : ℝ)*(sp_s2_13) + (104405311/1000000000000 : ℝ)*(sp_s2_15) + (91123483/1000000000000 : ℝ)*(sp_s2_23) + (2938619719783/1000000000000 : ℝ)*(f.failure) + (1755633891603/250000000000 : ℝ)*(f.sum) + (10344291876735264677/20997777900000000000000000000000 : ℝ)*base62 + (137580763160097/267025000000000000000000000 : ℝ)*base64 + (17271307355543/1310600000000000000000000000 : ℝ)*base66 + (3167510873149837/6408600000000000000000000000 : ℝ)*base68 + (26733811145820436497/65116716500000000000000000000000 : ℝ)*base70 + (2856567992781363/6096500000000000000000000000 : ℝ)*base72 + (362685335866971/1310600000000000000000000000 : ℝ)*base74 + (714810277563167/6096500000000000000000000000 : ℝ)*base76 + (4911304580697798173/79900729000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (38679/100000000000000000 : ℝ)*base86 + (38679/100000000000000000 : ℝ)*base88 + (38679/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(807/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(807/2000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1093883959937542172858804479309/85341968644900000000000000000000000 : ℝ) := by norm_num
    linear_combination (842613/1000000000000 : ℝ)*(base39) + (10831937997/125000000000 : ℝ)*(base49) + (1360995427/8000000000 : ℝ)*(base59) + (4842013152989/1000000000000 : ℝ)*(major_s2_0) + (4842013152989/1000000000000 : ℝ)*(major_s2_1) + (4842013152989/1000000000000 : ℝ)*(major_s2_2) + (11861959/500000000000 : ℝ)*(sp_s2_1) + (3223011/100000000000 : ℝ)*(sp_s2_2) + (64911381/1000000000000 : ℝ)*(sp_s2_7) + (426693317719/62500000000 : ℝ)*(sp_s2_14) + (853391783871/125000000000 : ℝ)*(sp_s2_15) + (273085030591/40000000000 : ℝ)*(sp_s2_16) + (714190905471/250000000000 : ℝ)*(sp_s2_20) + (100416649/1000000000000 : ℝ)*(sp_s2_27) + (2856864038533/1000000000000 : ℝ)*(f.failure) + (1365431598977/200000000000 : ℝ)*(f.sum) + (293634223229377033/20997777900000000000000000000000 : ℝ)*base63 + (244784582092143/267025000000000000000000000 : ℝ)*base65 + (745402045771937/1310600000000000000000000000 : ℝ)*base67 + (1486897766417963/6408600000000000000000000000 : ℝ)*base69 + (29353364722772359043/65116716500000000000000000000000 : ℝ)*base71 + (2418727545016297/6096500000000000000000000000 : ℝ)*base73 + (948429738026889/1310600000000000000000000000 : ℝ)*base75 + (4157267741091073/6096500000000000000000000000 : ℝ)*base77 + (22901385334737394987/79900729000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (57429/100000000000000000 : ℝ)*base86 + (57429/100000000000000000 : ℝ)*base88 + (57429/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7739/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7739/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (491163453893831039418028058863/42670984322450000000000000000000000 : ℝ) := by norm_num
    linear_combination (207880531681/1000000000000 : ℝ)*(base40) + (5009209/1000000000000 : ℝ)*(base49) + (233508278849/1000000000000 : ℝ)*(base59) + (111202723879/25000000000 : ℝ)*(major_s2_0) + (111202723879/25000000000 : ℝ)*(major_s2_1) + (111202723879/25000000000 : ℝ)*(major_s2_2) + (28564391/1000000000000 : ℝ)*(sp_s2_0) + (44144857/1000000000000 : ℝ)*(sp_s2_2) + (3662757/250000000000 : ℝ)*(sp_s2_16) + (189772317/1000000000000 : ℝ)*(sp_s2_20) + (6271731152619/1000000000000 : ℝ)*(sp_s2_21) + (627175971701/100000000000 : ℝ)*(sp_s2_22) + (1567925230281/250000000000 : ℝ)*(sp_s2_23) + (1312132292079/500000000000 : ℝ)*(sp_s2_27) + (656113589119/250000000000 : ℝ)*(f.failure) + (627175971701/100000000000 : ℝ)*(f.sum) + (260995819300224031/419955558000000000000000000000 : ℝ)*base63 + (13678532775109/106810000000000000000000000 : ℝ)*base65 + (9272505780653/32765000000000000000000000 : ℝ)*base66 + (293051959481/801075000000000000000000 : ℝ)*base69 + (2692939171775801581/3255835825000000000000000000000 : ℝ)*base71 + (335452002246557/609650000000000000000000000 : ℝ)*base72 + (28220783972713/32765000000000000000000000 : ℝ)*base75 + (159234836427683/152412500000000000000000000 : ℝ)*base77 + (1247233937430812063/1997518225000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (11953/25000000000000000 : ℝ)*base87 + (11953/25000000000000000 : ℝ)*base89 + (11953/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((12193/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12193/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6553/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6553/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32043/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32043/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((34399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(34399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(807/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(807/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7739/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7739/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313053_s2 p hpa hpb X hX hprev1

#print axioms solution

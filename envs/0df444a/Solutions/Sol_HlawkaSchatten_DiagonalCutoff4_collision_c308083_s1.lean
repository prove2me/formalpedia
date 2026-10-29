-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:40:25.286731+00:00
-- url     : https://prove2.me/submissions/32e5e777-1998-4c03-99fd-354a77ac0df3

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
theorem collision_support_c308083_s1_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1907482119/10000000000 : ℝ)*x 0 + (5019351159/10000000000 : ℝ)*x 1 + (5660359773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1907482119/10000000000 : ℝ)^69 ≤ (11567539639739/100000000000000 : ℝ)^53 := by
    have hnat : (1907482119 : ℕ)^69*100000000000000^53 ≤ 11567539639739^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907482119 10000000000 11567539639739 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5019351159/10000000000 : ℝ)^69 ≤ (20382011533999/50000000000000 : ℝ)^53 := by
    have hnat : (5019351159 : ℕ)^69*50000000000000^53 ≤ 20382011533999^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019351159 10000000000 20382011533999 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660359773/10000000000 : ℝ)^69 ≤ (11917109319501/25000000000000 : ℝ)^53 := by
    have hnat : (5660359773 : ℕ)^69*25000000000000^53 ≤ 11917109319501^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660359773 10000000000 11917109319501 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1907482119/10000000000 : ℝ), (5019351159/10000000000 : ℝ), (5660359773/10000000000 : ℝ)] ![(11567539639739/100000000000000 : ℝ), (20382011533999/50000000000000 : ℝ), (11917109319501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1907482119/10000000000 : ℝ)|^69 ≤ (11567539639739/100000000000000 : ℝ)^53
        have hw : |(-1907482119/10000000000 : ℝ)|=(1907482119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5019351159/10000000000 : ℝ)|^69 ≤ (20382011533999/50000000000000 : ℝ)^53
        have hw : |(5019351159/10000000000 : ℝ)|=(5019351159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660359773/10000000000 : ℝ)|^69 ≤ (11917109319501/25000000000000 : ℝ)^53
        have hw : |(5660359773/10000000000 : ℝ)|=(5660359773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (707196943/2000000000 : ℝ)*x 0 + (3448181583/5000000000 : ℝ)*x 1 + (-1013458739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (707196943/2000000000 : ℝ)^69 ≤ (25835187958827/100000000000000 : ℝ)^53 := by
    have hnat : (707196943 : ℕ)^69*100000000000000^53 ≤ 25835187958827^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707196943 2000000000 25835187958827 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3448181583/5000000000 : ℝ)^69 ≤ (61645541289187/100000000000000 : ℝ)^53 := by
    have hnat : (3448181583 : ℕ)^69*100000000000000^53 ≤ 61645541289187^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448181583 5000000000 61645541289187 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013458739/5000000000 : ℝ)^69 ≤ (6259635368227/50000000000000 : ℝ)^53 := by
    have hnat : (1013458739 : ℕ)^69*50000000000000^53 ≤ 6259635368227^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013458739 5000000000 6259635368227 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(707196943/2000000000 : ℝ), (3448181583/5000000000 : ℝ), (-1013458739/5000000000 : ℝ)] ![(25835187958827/100000000000000 : ℝ), (61645541289187/100000000000000 : ℝ), (6259635368227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(707196943/2000000000 : ℝ)|^69 ≤ (25835187958827/100000000000000 : ℝ)^53
        have hw : |(707196943/2000000000 : ℝ)|=(707196943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3448181583/5000000000 : ℝ)|^69 ≤ (61645541289187/100000000000000 : ℝ)^53
        have hw : |(3448181583/5000000000 : ℝ)|=(3448181583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1013458739/5000000000 : ℝ)|^69 ≤ (6259635368227/50000000000000 : ℝ)^53
        have hw : |(-1013458739/5000000000 : ℝ)|=(1013458739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3132373273/10000000000 : ℝ)*x 0 + (1162509153/2500000000 : ℝ)*x 1 + (157648043/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3132373273/10000000000 : ℝ)^69 ≤ (11032003345667/50000000000000 : ℝ)^53 := by
    have hnat : (3132373273 : ℕ)^69*50000000000000^53 ≤ 11032003345667^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3132373273 10000000000 11032003345667 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1162509153/2500000000 : ℝ)^69 ≤ (36903354334857/100000000000000 : ℝ)^53 := by
    have hnat : (1162509153 : ℕ)^69*100000000000000^53 ≤ 36903354334857^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162509153 2500000000 36903354334857 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157648043/312500000 : ℝ)^69 ≤ (20516319479583/50000000000000 : ℝ)^53 := by
    have hnat : (157648043 : ℕ)^69*50000000000000^53 ≤ 20516319479583^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157648043 312500000 20516319479583 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3132373273/10000000000 : ℝ), (1162509153/2500000000 : ℝ), (157648043/312500000 : ℝ)] ![(11032003345667/50000000000000 : ℝ), (36903354334857/100000000000000 : ℝ), (20516319479583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3132373273/10000000000 : ℝ)|^69 ≤ (11032003345667/50000000000000 : ℝ)^53
        have hw : |(3132373273/10000000000 : ℝ)|=(3132373273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1162509153/2500000000 : ℝ)|^69 ≤ (36903354334857/100000000000000 : ℝ)^53
        have hw : |(1162509153/2500000000 : ℝ)|=(1162509153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157648043/312500000 : ℝ)|^69 ≤ (20516319479583/50000000000000 : ℝ)^53
        have hw : |(157648043/312500000 : ℝ)|=(157648043/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1324750321/5000000000 : ℝ)*x 0 + (3638351997/10000000000 : ℝ)*x 1 + (1589243027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324750321/5000000000 : ℝ)^69 ≤ (17742910753223/100000000000000 : ℝ)^53 := by
    have hnat : (1324750321 : ℕ)^69*100000000000000^53 ≤ 17742910753223^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324750321 5000000000 17742910753223 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3638351997/10000000000 : ℝ)^69 ≤ (335164226553/1250000000000 : ℝ)^53 := by
    have hnat : (3638351997 : ℕ)^69*1250000000000^53 ≤ 335164226553^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3638351997 10000000000 335164226553 1250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1589243027/2500000000 : ℝ)^69 ≤ (3465246944021/6250000000000 : ℝ)^53 := by
    have hnat : (1589243027 : ℕ)^69*6250000000000^53 ≤ 3465246944021^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589243027 2500000000 3465246944021 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1324750321/5000000000 : ℝ), (3638351997/10000000000 : ℝ), (1589243027/2500000000 : ℝ)] ![(17742910753223/100000000000000 : ℝ), (335164226553/1250000000000 : ℝ), (3465246944021/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1324750321/5000000000 : ℝ)|^69 ≤ (17742910753223/100000000000000 : ℝ)^53
        have hw : |(-1324750321/5000000000 : ℝ)|=(1324750321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3638351997/10000000000 : ℝ)|^69 ≤ (335164226553/1250000000000 : ℝ)^53
        have hw : |(3638351997/10000000000 : ℝ)|=(3638351997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1589243027/2500000000 : ℝ)|^69 ≤ (3465246944021/6250000000000 : ℝ)^53
        have hw : |(1589243027/2500000000 : ℝ)|=(1589243027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5697666507/10000000000 : ℝ)*x 0 + (7720907/2000000000 : ℝ)*x 1 + (6038012981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5697666507/10000000000 : ℝ)^69 ≤ (48077866195507/100000000000000 : ℝ)^53 := by
    have hnat : (5697666507 : ℕ)^69*100000000000000^53 ≤ 48077866195507^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697666507 10000000000 48077866195507 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7720907/2000000000 : ℝ)^69 ≤ (18030854939/25000000000000 : ℝ)^53 := by
    have hnat : (7720907 : ℕ)^69*25000000000000^53 ≤ 18030854939^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7720907 2000000000 18030854939 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6038012981/10000000000 : ℝ)^69 ≤ (10370002074677/20000000000000 : ℝ)^53 := by
    have hnat : (6038012981 : ℕ)^69*20000000000000^53 ≤ 10370002074677^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6038012981 10000000000 10370002074677 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5697666507/10000000000 : ℝ), (7720907/2000000000 : ℝ), (6038012981/10000000000 : ℝ)] ![(48077866195507/100000000000000 : ℝ), (18030854939/25000000000000 : ℝ), (10370002074677/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5697666507/10000000000 : ℝ)|^69 ≤ (48077866195507/100000000000000 : ℝ)^53
        have hw : |(5697666507/10000000000 : ℝ)|=(5697666507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7720907/2000000000 : ℝ)|^69 ≤ (18030854939/25000000000000 : ℝ)^53
        have hw : |(7720907/2000000000 : ℝ)|=(7720907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6038012981/10000000000 : ℝ)|^69 ≤ (10370002074677/20000000000000 : ℝ)^53
        have hw : |(6038012981/10000000000 : ℝ)|=(6038012981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (715037807/5000000000 : ℝ)*x 0 + (8645308861/10000000000 : ℝ)*x 1 + (-1614980673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (715037807/5000000000 : ℝ)^69 ≤ (124220440529/1562500000000 : ℝ)^53 := by
    have hnat : (715037807 : ℕ)^69*1562500000000^53 ≤ 124220440529^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715037807 5000000000 124220440529 1562500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8645308861/10000000000 : ℝ)^69 ≤ (41368082391933/50000000000000 : ℝ)^53 := by
    have hnat : (8645308861 : ℕ)^69*50000000000000^53 ≤ 41368082391933^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8645308861 10000000000 41368082391933 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1614980673/10000000000 : ℝ)^69 ≤ (9313727006987/100000000000000 : ℝ)^53 := by
    have hnat : (1614980673 : ℕ)^69*100000000000000^53 ≤ 9313727006987^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614980673 10000000000 9313727006987 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(715037807/5000000000 : ℝ), (8645308861/10000000000 : ℝ), (-1614980673/10000000000 : ℝ)] ![(124220440529/1562500000000 : ℝ), (41368082391933/50000000000000 : ℝ), (9313727006987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(715037807/5000000000 : ℝ)|^69 ≤ (124220440529/1562500000000 : ℝ)^53
        have hw : |(715037807/5000000000 : ℝ)|=(715037807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8645308861/10000000000 : ℝ)|^69 ≤ (41368082391933/50000000000000 : ℝ)^53
        have hw : |(8645308861/10000000000 : ℝ)|=(8645308861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1614980673/10000000000 : ℝ)|^69 ≤ (9313727006987/100000000000000 : ℝ)^53
        have hw : |(-1614980673/10000000000 : ℝ)|=(1614980673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (548892681/2000000000 : ℝ)*x 0 + (376076191/625000000 : ℝ)*x 1 + (986634347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548892681/2000000000 : ℝ)^69 ≤ (4643817800321/25000000000000 : ℝ)^53 := by
    have hnat : (548892681 : ℕ)^69*25000000000000^53 ≤ 4643817800321^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548892681 2000000000 4643817800321 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376076191/625000000 : ℝ)^69 ≤ (51617662606491/100000000000000 : ℝ)^53 := by
    have hnat : (376076191 : ℕ)^69*100000000000000^53 ≤ 51617662606491^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376076191 625000000 51617662606491 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986634347/2500000000 : ℝ)^69 ≤ (29807066175359/100000000000000 : ℝ)^53 := by
    have hnat : (986634347 : ℕ)^69*100000000000000^53 ≤ 29807066175359^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986634347 2500000000 29807066175359 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(548892681/2000000000 : ℝ), (376076191/625000000 : ℝ), (986634347/2500000000 : ℝ)] ![(4643817800321/25000000000000 : ℝ), (51617662606491/100000000000000 : ℝ), (29807066175359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(548892681/2000000000 : ℝ)|^69 ≤ (4643817800321/25000000000000 : ℝ)^53
        have hw : |(548892681/2000000000 : ℝ)|=(548892681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(376076191/625000000 : ℝ)|^69 ≤ (51617662606491/100000000000000 : ℝ)^53
        have hw : |(376076191/625000000 : ℝ)|=(376076191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(986634347/2500000000 : ℝ)|^69 ≤ (29807066175359/100000000000000 : ℝ)^53
        have hw : |(986634347/2500000000 : ℝ)|=(986634347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-489186229/10000000000 : ℝ)*x 0 + (42143933/156250000 : ℝ)*x 1 + (841455479/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489186229/10000000000 : ℝ)^69 ≤ (491794659287/25000000000000 : ℝ)^53 := by
    have hnat : (489186229 : ℕ)^69*25000000000000^53 ≤ 491794659287^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489186229 10000000000 491794659287 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42143933/156250000 : ℝ)^69 ≤ (9079999131907/50000000000000 : ℝ)^53 := by
    have hnat : (42143933 : ℕ)^69*50000000000000^53 ≤ 9079999131907^53*156250000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42143933 156250000 9079999131907 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (841455479/1000000000 : ℝ)^69 ≤ (15974564616441/20000000000000 : ℝ)^53 := by
    have hnat : (841455479 : ℕ)^69*20000000000000^53 ≤ 15974564616441^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841455479 1000000000 15974564616441 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489186229/10000000000 : ℝ), (42143933/156250000 : ℝ), (841455479/1000000000 : ℝ)] ![(491794659287/25000000000000 : ℝ), (9079999131907/50000000000000 : ℝ), (15974564616441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489186229/10000000000 : ℝ)|^69 ≤ (491794659287/25000000000000 : ℝ)^53
        have hw : |(-489186229/10000000000 : ℝ)|=(489186229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42143933/156250000 : ℝ)|^69 ≤ (9079999131907/50000000000000 : ℝ)^53
        have hw : |(42143933/156250000 : ℝ)|=(42143933/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(841455479/1000000000 : ℝ)|^69 ≤ (15974564616441/20000000000000 : ℝ)^53
        have hw : |(841455479/1000000000 : ℝ)|=(841455479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2215395007/2500000000 : ℝ)*x 0 + (151717/5000000000 : ℝ)*x 1 + (2276086699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215395007/2500000000 : ℝ)^69 ≤ (85440833728441/100000000000000 : ℝ)^53 := by
    have hnat : (2215395007 : ℕ)^69*100000000000000^53 ≤ 85440833728441^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215395007 2500000000 85440833728441 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151717/5000000000 : ℝ)^69 ≤ (131268073/100000000000000 : ℝ)^53 := by
    have hnat : (151717 : ℕ)^69*100000000000000^53 ≤ 131268073^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151717 5000000000 131268073 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276086699/10000000000 : ℝ)^69 ≤ (29118069981/200000000000 : ℝ)^53 := by
    have hnat : (2276086699 : ℕ)^69*200000000000^53 ≤ 29118069981^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276086699 10000000000 29118069981 200000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2215395007/2500000000 : ℝ), (151717/5000000000 : ℝ), (2276086699/10000000000 : ℝ)] ![(85440833728441/100000000000000 : ℝ), (131268073/100000000000000 : ℝ), (29118069981/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2215395007/2500000000 : ℝ)|^69 ≤ (85440833728441/100000000000000 : ℝ)^53
        have hw : |(2215395007/2500000000 : ℝ)|=(2215395007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(151717/5000000000 : ℝ)|^69 ≤ (131268073/100000000000000 : ℝ)^53
        have hw : |(151717/5000000000 : ℝ)|=(151717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2276086699/10000000000 : ℝ)|^69 ≤ (29118069981/200000000000 : ℝ)^53
        have hw : |(2276086699/10000000000 : ℝ)|=(2276086699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1180787409/2500000000 : ℝ)*x 0 + (3255519131/5000000000 : ℝ)*x 1 + (-1022951001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1180787409/2500000000 : ℝ)^69 ≤ (4707567676043/12500000000000 : ℝ)^53 := by
    have hnat : (1180787409 : ℕ)^69*12500000000000^53 ≤ 4707567676043^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180787409 2500000000 4707567676043 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3255519131/5000000000 : ℝ)^69 ≤ (28599847852921/50000000000000 : ℝ)^53 := by
    have hnat : (3255519131 : ℕ)^69*50000000000000^53 ≤ 28599847852921^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3255519131 5000000000 28599847852921 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022951001/10000000000 : ℝ)^69 ≤ (1027952574079/20000000000000 : ℝ)^53 := by
    have hnat : (1022951001 : ℕ)^69*20000000000000^53 ≤ 1027952574079^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022951001 10000000000 1027952574079 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1180787409/2500000000 : ℝ), (3255519131/5000000000 : ℝ), (-1022951001/10000000000 : ℝ)] ![(4707567676043/12500000000000 : ℝ), (28599847852921/50000000000000 : ℝ), (1027952574079/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1180787409/2500000000 : ℝ)|^69 ≤ (4707567676043/12500000000000 : ℝ)^53
        have hw : |(1180787409/2500000000 : ℝ)|=(1180787409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3255519131/5000000000 : ℝ)|^69 ≤ (28599847852921/50000000000000 : ℝ)^53
        have hw : |(3255519131/5000000000 : ℝ)|=(3255519131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022951001/10000000000 : ℝ)|^69 ≤ (1027952574079/20000000000000 : ℝ)^53
        have hw : |(-1022951001/10000000000 : ℝ)|=(1022951001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (573917457/2000000000 : ℝ)*x 0 + (3229818511/10000000000 : ℝ)*x 1 + (6524430563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (573917457/2000000000 : ℝ)^69 ≤ (19685311386539/100000000000000 : ℝ)^53 := by
    have hnat : (573917457 : ℕ)^69*100000000000000^53 ≤ 19685311386539^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573917457 2000000000 19685311386539 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3229818511/10000000000 : ℝ)^69 ≤ (22961776004983/100000000000000 : ℝ)^53 := by
    have hnat : (3229818511 : ℕ)^69*100000000000000^53 ≤ 22961776004983^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3229818511 10000000000 22961776004983 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6524430563/10000000000 : ℝ)^69 ≤ (57352912596171/100000000000000 : ℝ)^53 := by
    have hnat : (6524430563 : ℕ)^69*100000000000000^53 ≤ 57352912596171^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6524430563 10000000000 57352912596171 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(573917457/2000000000 : ℝ), (3229818511/10000000000 : ℝ), (6524430563/10000000000 : ℝ)] ![(19685311386539/100000000000000 : ℝ), (22961776004983/100000000000000 : ℝ), (57352912596171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(573917457/2000000000 : ℝ)|^69 ≤ (19685311386539/100000000000000 : ℝ)^53
        have hw : |(573917457/2000000000 : ℝ)|=(573917457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3229818511/10000000000 : ℝ)|^69 ≤ (22961776004983/100000000000000 : ℝ)^53
        have hw : |(3229818511/10000000000 : ℝ)|=(3229818511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6524430563/10000000000 : ℝ)|^69 ≤ (57352912596171/100000000000000 : ℝ)^53
        have hw : |(6524430563/10000000000 : ℝ)|=(6524430563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-299840569/2000000000 : ℝ)*x 0 + (1626844789/2500000000 : ℝ)*x 1 + (880923049/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (299840569/2000000000 : ℝ)^69 ≤ (8454025172137/100000000000000 : ℝ)^53 := by
    have hnat : (299840569 : ℕ)^69*100000000000000^53 ≤ 8454025172137^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299840569 2000000000 8454025172137 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1626844789/2500000000 : ℝ)^69 ≤ (7144731202567/12500000000000 : ℝ)^53 := by
    have hnat : (1626844789 : ℕ)^69*12500000000000^53 ≤ 7144731202567^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1626844789 2500000000 7144731202567 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880923049/2000000000 : ℝ)^69 ≤ (17194062596489/50000000000000 : ℝ)^53 := by
    have hnat : (880923049 : ℕ)^69*50000000000000^53 ≤ 17194062596489^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880923049 2000000000 17194062596489 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-299840569/2000000000 : ℝ), (1626844789/2500000000 : ℝ), (880923049/2000000000 : ℝ)] ![(8454025172137/100000000000000 : ℝ), (7144731202567/12500000000000 : ℝ), (17194062596489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-299840569/2000000000 : ℝ)|^69 ≤ (8454025172137/100000000000000 : ℝ)^53
        have hw : |(-299840569/2000000000 : ℝ)|=(299840569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1626844789/2500000000 : ℝ)|^69 ≤ (7144731202567/12500000000000 : ℝ)^53
        have hw : |(1626844789/2500000000 : ℝ)|=(1626844789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(880923049/2000000000 : ℝ)|^69 ≤ (17194062596489/50000000000000 : ℝ)^53
        have hw : |(880923049/2000000000 : ℝ)|=(880923049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (532642937/625000000 : ℝ)*x 0 + (1669989/5000000000 : ℝ)*x 1 + (2768833741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532642937/625000000 : ℝ)^69 ≤ (81206721167911/100000000000000 : ℝ)^53 := by
    have hnat : (532642937 : ℕ)^69*100000000000000^53 ≤ 81206721167911^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532642937 625000000 81206721167911 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1669989/5000000000 : ℝ)^69 ≤ (2980627567/100000000000000 : ℝ)^53 := by
    have hnat : (1669989 : ℕ)^69*100000000000000^53 ≤ 2980627567^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669989 5000000000 2980627567 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2768833741/10000000000 : ℝ)^69 ≤ (9395149096031/50000000000000 : ℝ)^53 := by
    have hnat : (2768833741 : ℕ)^69*50000000000000^53 ≤ 9395149096031^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768833741 10000000000 9395149096031 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532642937/625000000 : ℝ), (1669989/5000000000 : ℝ), (2768833741/10000000000 : ℝ)] ![(81206721167911/100000000000000 : ℝ), (2980627567/100000000000000 : ℝ), (9395149096031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532642937/625000000 : ℝ)|^69 ≤ (81206721167911/100000000000000 : ℝ)^53
        have hw : |(532642937/625000000 : ℝ)|=(532642937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1669989/5000000000 : ℝ)|^69 ≤ (2980627567/100000000000000 : ℝ)^53
        have hw : |(1669989/5000000000 : ℝ)|=(1669989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2768833741/10000000000 : ℝ)|^69 ≤ (9395149096031/50000000000000 : ℝ)^53
        have hw : |(2768833741/10000000000 : ℝ)|=(2768833741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (429453113/2000000000 : ℝ)*x 0 + (784652313/1000000000 : ℝ)*x 1 + (-4314803/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429453113/2000000000 : ℝ)^69 ≤ (674777975289/5000000000000 : ℝ)^53 := by
    have hnat : (429453113 : ℕ)^69*5000000000000^53 ≤ 674777975289^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429453113 2000000000 674777975289 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (784652313/1000000000 : ℝ)^69 ≤ (56973348533/78125000000 : ℝ)^53 := by
    have hnat : (784652313 : ℕ)^69*78125000000^53 ≤ 56973348533^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784652313 1000000000 56973348533 78125000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4314803/20000000 : ℝ)^69 ≤ (1357855435949/10000000000000 : ℝ)^53 := by
    have hnat : (4314803 : ℕ)^69*10000000000000^53 ≤ 1357855435949^53*20000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314803 20000000 1357855435949 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429453113/2000000000 : ℝ), (784652313/1000000000 : ℝ), (-4314803/20000000 : ℝ)] ![(674777975289/5000000000000 : ℝ), (56973348533/78125000000 : ℝ), (1357855435949/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429453113/2000000000 : ℝ)|^69 ≤ (674777975289/5000000000000 : ℝ)^53
        have hw : |(429453113/2000000000 : ℝ)|=(429453113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(784652313/1000000000 : ℝ)|^69 ≤ (56973348533/78125000000 : ℝ)^53
        have hw : |(784652313/1000000000 : ℝ)|=(784652313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4314803/20000000 : ℝ)|^69 ≤ (1357855435949/10000000000000 : ℝ)^53
        have hw : |(-4314803/20000000 : ℝ)|=(4314803/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308083_s1_s1_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1223207493/2000000000 : ℝ)*x 0 + (44784573/125000000 : ℝ)*x 1 + (94222713/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1223207493/2000000000 : ℝ)^69 ≤ (10544798551543/20000000000000 : ℝ)^53 := by
    have hnat : (1223207493 : ℕ)^69*20000000000000^53 ≤ 10544798551543^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223207493 2000000000 10544798551543 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44784573/125000000 : ℝ)^69 ≤ (6570264654247/25000000000000 : ℝ)^53 := by
    have hnat : (44784573 : ℕ)^69*25000000000000^53 ≤ 6570264654247^53*125000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44784573 125000000 6570264654247 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94222713/312500000 : ℝ)^69 ≤ (20994948609693/100000000000000 : ℝ)^53 := by
    have hnat : (94222713 : ℕ)^69*100000000000000^53 ≤ 20994948609693^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94222713 312500000 20994948609693 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1223207493/2000000000 : ℝ), (44784573/125000000 : ℝ), (94222713/312500000 : ℝ)] ![(10544798551543/20000000000000 : ℝ), (6570264654247/25000000000000 : ℝ), (20994948609693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1223207493/2000000000 : ℝ)|^69 ≤ (10544798551543/20000000000000 : ℝ)^53
        have hw : |(1223207493/2000000000 : ℝ)|=(1223207493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44784573/125000000 : ℝ)|^69 ≤ (6570264654247/25000000000000 : ℝ)^53
        have hw : |(44784573/125000000 : ℝ)|=(44784573/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94222713/312500000 : ℝ)|^69 ≤ (20994948609693/100000000000000 : ℝ)^53
        have hw : |(94222713/312500000 : ℝ)|=(94222713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308083_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((40423/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40423/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((8527/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(8527/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(89911/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(89911/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15677/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15677/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((62331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(62331/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70981/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(70981/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (40423/50000 : ℝ) ^ (17/4 : ℝ) ≤ (10127186131320182911/25000000000000000000 : ℝ) := by
    have hpowers : (40423/50000 : ℝ)^17 ≤ (10127186131320182911/25000000000000000000 : ℝ)^4 := by
      have hnat : (40423 : ℕ)^17*25000000000000000000^4 ≤ 10127186131320182911^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40423 50000 10127186131320182911 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40423/50000 : ℝ)) (X := (10127186131320182911/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (35127186131320182911/25000000000000000000 : ℝ) ≤ (5416562198463987/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (35127186131320182911/25000000000000000000 : ℝ)^4 ≤ (5416562198463987/5000000000000000 : ℝ)^17 := by
      have hnat : (35127186131320182911 : ℕ)^4*5000000000000000^17 ≤ 5416562198463987^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35127186131320182911 25000000000000000000 5416562198463987 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5416562198463987/5000000000000000 : ℝ)) (X := (35127186131320182911/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (22627186131320182911/12500000000000000000 : ℝ) ≤ (11498471846529551/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (22627186131320182911/12500000000000000000 : ℝ)^4 ≤ (11498471846529551/10000000000000000 : ℝ)^17 := by
      have hnat : (22627186131320182911 : ℕ)^4*10000000000000000^17 ≤ 11498471846529551^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22627186131320182911 12500000000000000000 11498471846529551 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11498471846529551/10000000000000000 : ℝ)) (X := (22627186131320182911/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(416562198463987/4042300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(665347449601577/8084600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (40423/50000 : ℝ)) (alpha := (416562198463987/4042300000000000 : ℝ)) (beta := (665347449601577/8084600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (40423/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(416562198463987/4042300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(665347449601577/8084600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8527/10000 : ℝ) ^ (17/4 : ℝ) ≤ (1016047738042607669/2000000000000000000 : ℝ) := by
    have hpowers : (8527/10000 : ℝ)^17 ≤ (1016047738042607669/2000000000000000000 : ℝ)^4 := by
      have hnat : (8527 : ℕ)^17*2000000000000000000^4 ≤ 1016047738042607669^4*10000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8527 10000 1016047738042607669 2000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8527/10000 : ℝ)) (X := (1016047738042607669/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3016047738042607669/2000000000000000000 : ℝ) ≤ (11014845342367973/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3016047738042607669/2000000000000000000 : ℝ)^4 ≤ (11014845342367973/10000000000000000 : ℝ)^17 := by
      have hnat : (3016047738042607669 : ℕ)^4*10000000000000000^17 ≤ 11014845342367973^17*2000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3016047738042607669 2000000000000000000 11014845342367973 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11014845342367973/10000000000000000 : ℝ)) (X := (3016047738042607669/2000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2016047738042607669/1000000000000000000 : ℝ) ≤ (11793623243302979/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2016047738042607669/1000000000000000000 : ℝ)^4 ≤ (11793623243302979/10000000000000000 : ℝ)^17 := by
      have hnat : (2016047738042607669 : ℕ)^4*10000000000000000^17 ≤ 11793623243302979^17*1000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2016047738042607669 1000000000000000000 11793623243302979 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11793623243302979/10000000000000000 : ℝ)) (X := (2016047738042607669/1000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1014845342367973/8527000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(389388950467503/4263500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (8527/10000 : ℝ)) (alpha := (1014845342367973/8527000000000000 : ℝ)) (beta := (389388950467503/4263500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (8527/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1014845342367973/8527000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(389388950467503/4263500000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (89911/100000 : ℝ) ^ (17/4 : ℝ) ≤ (63636241137016734029/100000000000000000000 : ℝ) := by
    have hpowers : (89911/100000 : ℝ)^17 ≤ (63636241137016734029/100000000000000000000 : ℝ)^4 := by
      have hnat : (89911 : ℕ)^17*100000000000000000000^4 ≤ 63636241137016734029^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89911 100000 63636241137016734029 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89911/100000 : ℝ)) (X := (63636241137016734029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (163636241137016734029/100000000000000000000 : ℝ) ≤ (1122857352263609/1000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (163636241137016734029/100000000000000000000 : ℝ)^4 ≤ (1122857352263609/1000000000000000 : ℝ)^17 := by
      have hnat : (163636241137016734029 : ℕ)^4*1000000000000000^17 ≤ 1122857352263609^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        163636241137016734029 100000000000000000000 1122857352263609 1000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1122857352263609/1000000000000000 : ℝ)) (X := (163636241137016734029/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (113636241137016734029/50000000000000000000 : ℝ) ≤ (6065454958759499/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (113636241137016734029/50000000000000000000 : ℝ)^4 ≤ (6065454958759499/5000000000000000 : ℝ)^17 := by
      have hnat : (113636241137016734029 : ℕ)^4*5000000000000000^17 ≤ 6065454958759499^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113636241137016734029 50000000000000000000 6065454958759499 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6065454958759499/5000000000000000 : ℝ)) (X := (113636241137016734029/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(122857352263609/899110000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(225584098720727/2247775000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (89911/100000 : ℝ)) (alpha := (122857352263609/899110000000000 : ℝ)) (beta := (225584098720727/2247775000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (89911/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(122857352263609/899110000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(225584098720727/2247775000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1907482119/10000000000 : ℝ)*X 0 0+(5019351159/10000000000 : ℝ)*X 0 1+(5660359773/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((707196943/2000000000 : ℝ)*X 2 0+(3448181583/5000000000 : ℝ)*X 2 1+(-1013458739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3132373273/10000000000 : ℝ)*X 0 0+(1162509153/2500000000 : ℝ)*X 0 1+(157648043/312500000 : ℝ)*X 0 2+(3132373273/10000000000 : ℝ)*X 1 0+(1162509153/2500000000 : ℝ)*X 1 1+(157648043/312500000 : ℝ)*X 1 2+(3132373273/10000000000 : ℝ)*X 2 0+(1162509153/2500000000 : ℝ)*X 2 1+(157648043/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1324750321/5000000000 : ℝ)*X 0 0+(3638351997/10000000000 : ℝ)*X 0 1+(1589243027/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5697666507/10000000000 : ℝ)*X 1 0+(7720907/2000000000 : ℝ)*X 1 1+(6038012981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((715037807/5000000000 : ℝ)*X 2 0+(8645308861/10000000000 : ℝ)*X 2 1+(-1614980673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((548892681/2000000000 : ℝ)*X 0 0+(376076191/625000000 : ℝ)*X 0 1+(986634347/2500000000 : ℝ)*X 0 2+(548892681/2000000000 : ℝ)*X 1 0+(376076191/625000000 : ℝ)*X 1 1+(986634347/2500000000 : ℝ)*X 1 2+(548892681/2000000000 : ℝ)*X 2 0+(376076191/625000000 : ℝ)*X 2 1+(986634347/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-489186229/10000000000 : ℝ)*X 0 0+(42143933/156250000 : ℝ)*X 0 1+(841455479/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2215395007/2500000000 : ℝ)*X 1 0+(151717/5000000000 : ℝ)*X 1 1+(2276086699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1180787409/2500000000 : ℝ)*X 2 0+(3255519131/5000000000 : ℝ)*X 2 1+(-1022951001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((573917457/2000000000 : ℝ)*X 0 0+(3229818511/10000000000 : ℝ)*X 0 1+(6524430563/10000000000 : ℝ)*X 0 2+(573917457/2000000000 : ℝ)*X 1 0+(3229818511/10000000000 : ℝ)*X 1 1+(6524430563/10000000000 : ℝ)*X 1 2+(573917457/2000000000 : ℝ)*X 2 0+(3229818511/10000000000 : ℝ)*X 2 1+(6524430563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-299840569/2000000000 : ℝ)*X 0 0+(1626844789/2500000000 : ℝ)*X 0 1+(880923049/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((532642937/625000000 : ℝ)*X 1 0+(1669989/5000000000 : ℝ)*X 1 1+(2768833741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((429453113/2000000000 : ℝ)*X 2 0+(784652313/1000000000 : ℝ)*X 2 1+(-4314803/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1223207493/2000000000 : ℝ)*X 0 0+(44784573/125000000 : ℝ)*X 0 1+(94222713/312500000 : ℝ)*X 0 2+(1223207493/2000000000 : ℝ)*X 1 0+(44784573/125000000 : ℝ)*X 1 1+(94222713/312500000 : ℝ)*X 1 2+(1223207493/2000000000 : ℝ)*X 2 0+(44784573/125000000 : ℝ)*X 2 1+(94222713/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((15677/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15677/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (82466542804882912727690044990413/7747786438507750000000000000000000000 : ℝ) := by norm_num
    linear_combination (177726643259/250000000000 : ℝ)*(base7) + (4778583/500000000000 : ℝ)*(base23) + (356774248091/1000000000000 : ℝ)*(base49) + (188853270163/1000000000000 : ℝ)*(base60) + (259036806769/125000000000 : ℝ)*(major_s1_0) + (259036806769/125000000000 : ℝ)*(major_s1_1) + (259036806769/125000000000 : ℝ)*(major_s1_2) + (10975491/250000000000 : ℝ)*(sp_s1_0) + (22983621/1000000000000 : ℝ)*(sp_s1_6) + (2385492811459/1000000000000 : ℝ)*(sp_s1_7) + (1192775583839/500000000000 : ℝ)*(sp_s1_8) + (149096350657/62500000000 : ℝ)*(sp_s1_9) + (406650105731/200000000000 : ℝ)*(sp_s1_13) + (7227127/500000000000 : ℝ)*(sp_s1_14) + (33059173481/25000000000 : ℝ)*(f.failure) + (1192775583839/500000000000 : ℝ)*(f.sum) + (1000480005813153427/47916943562500000000000000000000 : ℝ)*base62 + (1142334601610163/4495550000000000000000000000 : ℝ)*base65 + (623951756495737/1065875000000000000000000000 : ℝ)*base67 + (51327561534063/449555000000000000000000000 : ℝ)*base68 + (7660005029514237557/90861808825000000000000000000000 : ℝ)*base70 + (45884602982571/505287500000000000000000000 : ℝ)*base72 + (39111933054993/532937500000000000000000000 : ℝ)*base75 + (27772050400053/126321875000000000000000000 : ℝ)*base76 + (847815775901743189/10771466281250000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (991/2500000000000000 : ℝ)*base87 + (991/2500000000000000 : ℝ)*base89 + (991/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((62331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(62331/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5546609836138555119163885776621/1549557287701550000000000000000000000 : ℝ) := by norm_num
    linear_combination (185160884821/500000000000 : ℝ)*(base7) + (3438197/500000000000 : ℝ)*(base33) + (22916145561/40000000000 : ℝ)*(base40) + (177543654119/1000000000000 : ℝ)*(base49) + (223724476201/500000000000 : ℝ)*(base60) + (1071309122343/500000000000 : ℝ)*(major_s1_0) + (53565628027/25000000000 : ℝ)*(major_s1_1) + (53565628027/25000000000 : ℝ)*(major_s1_2) + (6558101/1000000000000 : ℝ)*(sp_s1_2) + (672634112693/250000000000 : ℝ)*(sp_s1_14) + (336308665047/125000000000 : ℝ)*(sp_s1_15) + (672630754069/250000000000 : ℝ)*(sp_s1_16) + (1737567924079/1000000000000 : ℝ)*(sp_s1_20) + (30127001/500000000000 : ℝ)*(sp_s1_22) + (1367246154437/1000000000000 : ℝ)*(f.failure) + (672634112693/250000000000 : ℝ)*(f.sum) + (10304266187730422559/38333554850000000000000000000000 : ℝ)*base62 + (582210322735001/899110000000000000000000000 : ℝ)*base65 + (159677508497847/426350000000000000000000000 : ℝ)*base67 + (48443979457877/899110000000000000000000000 : ℝ)*base68 + (36403527285955587413/90861808825000000000000000000000 : ℝ)*base71 + (1306968889442821/4042300000000000000000000000 : ℝ)*base73 + (214149141068883/213175000000000000000000000 : ℝ)*base75 + (154729132290767/252643750000000000000000000 : ℝ)*base77 + (4706762937904351799/34468692100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (23293/100000000000000000 : ℝ)*base86 + (23293/100000000000000000 : ℝ)*base88 + (23293/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70981/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(70981/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (243820213375223142683113701/18172361765000000000000000000000 : ℝ) := by norm_num
    linear_combination (196461208773/250000000000 : ℝ)*(base7) + (6156001/1000000000000 : ℝ)*(base11) + (169528517497/500000000000 : ℝ)*(base40) + (261385959/2000000000 : ℝ)*(base49) + (10523/25000000000 : ℝ)*(base50) + (112336527779/50000000000 : ℝ)*(major_s1_0) + (112336527779/50000000000 : ℝ)*(major_s1_1) + (112336527779/50000000000 : ℝ)*(major_s1_2) + (48096883/500000000000 : ℝ)*(sp_s1_2) + (100893109/1000000000000 : ℝ)*(sp_s1_9) + (12885377591/5000000000 : ℝ)*(sp_s1_21) + (2577081674201/1000000000000 : ℝ)*(sp_s1_22) + (1288442293663/500000000000 : ℝ)*(sp_s1_23) + (88780898727/40000000000 : ℝ)*(sp_s1_27) + (716838816541/500000000000 : ℝ)*(f.failure) + (2577081674201/1000000000000 : ℝ)*(f.sum) + (2343213868949433189/38333554850000000000000000000000 : ℝ)*base62 + (30544469358817/112388750000000000000000000 : ℝ)*base64 + (92435417548967/426350000000000000000000000 : ℝ)*base67 + (347505325332517/899110000000000000000000000 : ℝ)*base68 + (964459044955905611/9086180882500000000000000000000 : ℝ)*base71 + (2689071221349/10105750000000000000000000 : ℝ)*base72 + (9333402891391/426350000000000000000000000 : ℝ)*base75 + (20158040315109/404230000000000000000000000 : ℝ)*base76 + (695403126127533729/17234346050000000000000000000000 : ℝ)*base78 + (43349/50000000000000000 : ℝ)*base86 + (43349/50000000000000000 : ℝ)*base88 + (43349/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((40423/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40423/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((8527/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(8527/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(89911/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(89911/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15677/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15677/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((62331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(62331/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70981/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(70981/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308083_s1 p hpa hpb X hX hprev0

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310082_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:08.384376+00:00
-- url     : https://prove2.me/submissions/9e27958e-59d2-460b-aeab-af6514bef0e1

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
theorem collision_support_c310082_s1_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-770165611/2000000000 : ℝ)*x 0 + (12707127/39062500 : ℝ)*x 1 + (1401245853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (770165611/2000000000 : ℝ)^71 ≤ (14586733868511/50000000000000 : ℝ)^55 := by
    have hnat : (770165611 : ℕ)^71*50000000000000^55 ≤ 14586733868511^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770165611 2000000000 14586733868511 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12707127/39062500 : ℝ)^71 ≤ (11732141500201/50000000000000 : ℝ)^55 := by
    have hnat : (12707127 : ℕ)^71*50000000000000^55 ≤ 11732141500201^55*39062500^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12707127 39062500 11732141500201 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401245853/2500000000 : ℝ)^71 ≤ (47362249251687/100000000000000 : ℝ)^55 := by
    have hnat : (1401245853 : ℕ)^71*100000000000000^55 ≤ 47362249251687^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401245853 2500000000 47362249251687 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-770165611/2000000000 : ℝ), (12707127/39062500 : ℝ), (1401245853/2500000000 : ℝ)] ![(14586733868511/50000000000000 : ℝ), (11732141500201/50000000000000 : ℝ), (47362249251687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-770165611/2000000000 : ℝ)|^71 ≤ (14586733868511/50000000000000 : ℝ)^55
        have hw : |(-770165611/2000000000 : ℝ)|=(770165611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12707127/39062500 : ℝ)|^71 ≤ (11732141500201/50000000000000 : ℝ)^55
        have hw : |(12707127/39062500 : ℝ)|=(12707127/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1401245853/2500000000 : ℝ)|^71 ≤ (47362249251687/100000000000000 : ℝ)^55
        have hw : |(1401245853/2500000000 : ℝ)|=(1401245853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (84521829/200000000 : ℝ)*x 0 + (-827725889/2500000000 : ℝ)*x 1 + (2605114677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84521829/200000000 : ℝ)^71 ≤ (16447167591181/50000000000000 : ℝ)^55 := by
    have hnat : (84521829 : ℕ)^71*50000000000000^55 ≤ 16447167591181^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84521829 200000000 16447167591181 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (827725889/2500000000 : ℝ)^71 ≤ (12002303822301/50000000000000 : ℝ)^55 := by
    have hnat : (827725889 : ℕ)^71*50000000000000^55 ≤ 12002303822301^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827725889 2500000000 12002303822301 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605114677/5000000000 : ℝ)^71 ≤ (673454018153/1562500000000 : ℝ)^55 := by
    have hnat : (2605114677 : ℕ)^71*1562500000000^55 ≤ 673454018153^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605114677 5000000000 673454018153 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84521829/200000000 : ℝ), (-827725889/2500000000 : ℝ), (2605114677/5000000000 : ℝ)] ![(16447167591181/50000000000000 : ℝ), (12002303822301/50000000000000 : ℝ), (673454018153/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84521829/200000000 : ℝ)|^71 ≤ (16447167591181/50000000000000 : ℝ)^55
        have hw : |(84521829/200000000 : ℝ)|=(84521829/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-827725889/2500000000 : ℝ)|^71 ≤ (12002303822301/50000000000000 : ℝ)^55
        have hw : |(-827725889/2500000000 : ℝ)|=(827725889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2605114677/5000000000 : ℝ)|^71 ≤ (673454018153/1562500000000 : ℝ)^55
        have hw : |(2605114677/5000000000 : ℝ)|=(2605114677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5948214141/10000000000 : ℝ)*x 0 + (5228925017/10000000000 : ℝ)*x 1 + (-1066292907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5948214141/10000000000 : ℝ)^71 ≤ (25569580852519/50000000000000 : ℝ)^55 := by
    have hnat : (5948214141 : ℕ)^71*50000000000000^55 ≤ 25569580852519^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5948214141 10000000000 25569580852519 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228925017/10000000000 : ℝ)^71 ≤ (4330081049329/10000000000000 : ℝ)^55 := by
    have hnat : (5228925017 : ℕ)^71*10000000000000^55 ≤ 4330081049329^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228925017 10000000000 4330081049329 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066292907/10000000000 : ℝ)^71 ≤ (2780013896779/50000000000000 : ℝ)^55 := by
    have hnat : (1066292907 : ℕ)^71*50000000000000^55 ≤ 2780013896779^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066292907 10000000000 2780013896779 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5948214141/10000000000 : ℝ), (5228925017/10000000000 : ℝ), (-1066292907/10000000000 : ℝ)] ![(25569580852519/50000000000000 : ℝ), (4330081049329/10000000000000 : ℝ), (2780013896779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5948214141/10000000000 : ℝ)|^71 ≤ (25569580852519/50000000000000 : ℝ)^55
        have hw : |(5948214141/10000000000 : ℝ)|=(5948214141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228925017/10000000000 : ℝ)|^71 ≤ (4330081049329/10000000000000 : ℝ)^55
        have hw : |(5228925017/10000000000 : ℝ)|=(5228925017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1066292907/10000000000 : ℝ)|^71 ≤ (2780013896779/50000000000000 : ℝ)^55
        have hw : |(-1066292907/10000000000 : ℝ)|=(1066292907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (753165529/10000000000 : ℝ)*x 0 + (5783588963/10000000000 : ℝ)*x 1 + (174492927/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (753165529/10000000000 : ℝ)^71 ≤ (3549503856587/100000000000000 : ℝ)^55 := by
    have hnat : (753165529 : ℕ)^71*100000000000000^55 ≤ 3549503856587^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753165529 10000000000 3549503856587 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5783588963/10000000000 : ℝ)^71 ≤ (49319479889567/100000000000000 : ℝ)^55 := by
    have hnat : (5783588963 : ℕ)^71*100000000000000^55 ≤ 49319479889567^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5783588963 10000000000 49319479889567 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174492927/312500000 : ℝ)^71 ≤ (47131016240961/100000000000000 : ℝ)^55 := by
    have hnat : (174492927 : ℕ)^71*100000000000000^55 ≤ 47131016240961^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174492927 312500000 47131016240961 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(753165529/10000000000 : ℝ), (5783588963/10000000000 : ℝ), (174492927/312500000 : ℝ)] ![(3549503856587/100000000000000 : ℝ), (49319479889567/100000000000000 : ℝ), (47131016240961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(753165529/10000000000 : ℝ)|^71 ≤ (3549503856587/100000000000000 : ℝ)^55
        have hw : |(753165529/10000000000 : ℝ)|=(753165529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5783588963/10000000000 : ℝ)|^71 ≤ (49319479889567/100000000000000 : ℝ)^55
        have hw : |(5783588963/10000000000 : ℝ)|=(5783588963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(174492927/312500000 : ℝ)|^71 ≤ (47131016240961/100000000000000 : ℝ)^55
        have hw : |(174492927/312500000 : ℝ)|=(174492927/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-27404469/78125000 : ℝ)*x 0 + (685094343/2500000000 : ℝ)*x 1 + (6322666999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27404469/78125000 : ℝ)^71 ≤ (206903022457/800000000000 : ℝ)^55 := by
    have hnat : (27404469 : ℕ)^71*800000000000^55 ≤ 206903022457^55*78125000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27404469 78125000 206903022457 800000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685094343/2500000000 : ℝ)^71 ≤ (4701152160623/25000000000000 : ℝ)^55 := by
    have hnat : (685094343 : ℕ)^71*25000000000000^55 ≤ 4701152160623^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685094343 2500000000 4701152160623 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6322666999/10000000000 : ℝ)^71 ≤ (27666256771721/50000000000000 : ℝ)^55 := by
    have hnat : (6322666999 : ℕ)^71*50000000000000^55 ≤ 27666256771721^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6322666999 10000000000 27666256771721 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27404469/78125000 : ℝ), (685094343/2500000000 : ℝ), (6322666999/10000000000 : ℝ)] ![(206903022457/800000000000 : ℝ), (4701152160623/25000000000000 : ℝ), (27666256771721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27404469/78125000 : ℝ)|^71 ≤ (206903022457/800000000000 : ℝ)^55
        have hw : |(-27404469/78125000 : ℝ)|=(27404469/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685094343/2500000000 : ℝ)|^71 ≤ (4701152160623/25000000000000 : ℝ)^55
        have hw : |(685094343/2500000000 : ℝ)|=(685094343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6322666999/10000000000 : ℝ)|^71 ≤ (27666256771721/50000000000000 : ℝ)^55
        have hw : |(6322666999/10000000000 : ℝ)|=(6322666999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5226523/12500000 : ℝ)*x 0 + (-1248449191/5000000000 : ℝ)*x 1 + (5924810353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226523/12500000 : ℝ)^71 ≤ (1622207535427/5000000000000 : ℝ)^55 := by
    have hnat : (5226523 : ℕ)^71*5000000000000^55 ≤ 1622207535427^55*12500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226523 12500000 1622207535427 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1248449191/5000000000 : ℝ)^71 ≤ (2084535594111/12500000000000 : ℝ)^55 := by
    have hnat : (1248449191 : ℕ)^71*12500000000000^55 ≤ 2084535594111^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248449191 5000000000 2084535594111 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5924810353/10000000000 : ℝ)^71 ≤ (50879564523591/100000000000000 : ℝ)^55 := by
    have hnat : (5924810353 : ℕ)^71*100000000000000^55 ≤ 50879564523591^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5924810353 10000000000 50879564523591 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226523/12500000 : ℝ), (-1248449191/5000000000 : ℝ), (5924810353/10000000000 : ℝ)] ![(1622207535427/5000000000000 : ℝ), (2084535594111/12500000000000 : ℝ), (50879564523591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226523/12500000 : ℝ)|^71 ≤ (1622207535427/5000000000000 : ℝ)^55
        have hw : |(5226523/12500000 : ℝ)|=(5226523/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1248449191/5000000000 : ℝ)|^71 ≤ (2084535594111/12500000000000 : ℝ)^55
        have hw : |(-1248449191/5000000000 : ℝ)|=(1248449191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5924810353/10000000000 : ℝ)|^71 ≤ (50879564523591/100000000000000 : ℝ)^55
        have hw : |(5924810353/10000000000 : ℝ)|=(5924810353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5632880317/10000000000 : ℝ)*x 0 + (1478482789/2500000000 : ℝ)*x 1 + (-50150263/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5632880317/10000000000 : ℝ)^71 ≤ (47666774702869/100000000000000 : ℝ)^55 := by
    have hnat : (5632880317 : ℕ)^71*100000000000000^55 ≤ 47666774702869^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5632880317 10000000000 47666774702869 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1478482789/2500000000 : ℝ)^71 ≤ (25379496413403/50000000000000 : ℝ)^55 := by
    have hnat : (1478482789 : ℕ)^71*50000000000000^55 ≤ 25379496413403^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1478482789 2500000000 25379496413403 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50150263/1250000000 : ℝ)^71 ≤ (1574232450989/100000000000000 : ℝ)^55 := by
    have hnat : (50150263 : ℕ)^71*100000000000000^55 ≤ 1574232450989^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50150263 1250000000 1574232450989 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5632880317/10000000000 : ℝ), (1478482789/2500000000 : ℝ), (-50150263/1250000000 : ℝ)] ![(47666774702869/100000000000000 : ℝ), (25379496413403/50000000000000 : ℝ), (1574232450989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5632880317/10000000000 : ℝ)|^71 ≤ (47666774702869/100000000000000 : ℝ)^55
        have hw : |(5632880317/10000000000 : ℝ)|=(5632880317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1478482789/2500000000 : ℝ)|^71 ≤ (25379496413403/50000000000000 : ℝ)^55
        have hw : |(1478482789/2500000000 : ℝ)|=(1478482789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50150263/1250000000 : ℝ)|^71 ≤ (1574232450989/100000000000000 : ℝ)^55
        have hw : |(-50150263/1250000000 : ℝ)|=(50150263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (161055241/10000000000 : ℝ)*x 0 + (371303061/500000000 : ℝ)*x 1 + (2038963423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161055241/10000000000 : ℝ)^71 ≤ (121145575629/25000000000000 : ℝ)^55 := by
    have hnat : (161055241 : ℕ)^71*25000000000000^55 ≤ 121145575629^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161055241 10000000000 121145575629 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (371303061/500000000 : ℝ)^71 ≤ (17025544648967/25000000000000 : ℝ)^55 := by
    have hnat : (371303061 : ℕ)^71*25000000000000^55 ≤ 17025544648967^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371303061 500000000 17025544648967 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2038963423/5000000000 : ℝ)^71 ≤ (6282647815593/20000000000000 : ℝ)^55 := by
    have hnat : (2038963423 : ℕ)^71*20000000000000^55 ≤ 6282647815593^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038963423 5000000000 6282647815593 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161055241/10000000000 : ℝ), (371303061/500000000 : ℝ), (2038963423/5000000000 : ℝ)] ![(121145575629/25000000000000 : ℝ), (17025544648967/25000000000000 : ℝ), (6282647815593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161055241/10000000000 : ℝ)|^71 ≤ (121145575629/25000000000000 : ℝ)^55
        have hw : |(161055241/10000000000 : ℝ)|=(161055241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(371303061/500000000 : ℝ)|^71 ≤ (17025544648967/25000000000000 : ℝ)^55
        have hw : |(371303061/500000000 : ℝ)|=(371303061/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2038963423/5000000000 : ℝ)|^71 ≤ (6282647815593/20000000000000 : ℝ)^55
        have hw : |(2038963423/5000000000 : ℝ)|=(2038963423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-676842567/2000000000 : ℝ)*x 0 + (727199789/2500000000 : ℝ)*x 1 + (6292982299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676842567/2000000000 : ℝ)^71 ≤ (12346465028857/50000000000000 : ℝ)^55 := by
    have hnat : (676842567 : ℕ)^71*50000000000000^55 ≤ 12346465028857^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676842567 2000000000 12346465028857 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (727199789/2500000000 : ℝ)^71 ≤ (10154842459013/50000000000000 : ℝ)^55 := by
    have hnat : (727199789 : ℕ)^71*50000000000000^55 ≤ 10154842459013^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727199789 2500000000 10154842459013 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6292982299/10000000000 : ℝ)^71 ≤ (54997385014189/100000000000000 : ℝ)^55 := by
    have hnat : (6292982299 : ℕ)^71*100000000000000^55 ≤ 54997385014189^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6292982299 10000000000 54997385014189 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-676842567/2000000000 : ℝ), (727199789/2500000000 : ℝ), (6292982299/10000000000 : ℝ)] ![(12346465028857/50000000000000 : ℝ), (10154842459013/50000000000000 : ℝ), (54997385014189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-676842567/2000000000 : ℝ)|^71 ≤ (12346465028857/50000000000000 : ℝ)^55
        have hw : |(-676842567/2000000000 : ℝ)|=(676842567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(727199789/2500000000 : ℝ)|^71 ≤ (10154842459013/50000000000000 : ℝ)^55
        have hw : |(727199789/2500000000 : ℝ)|=(727199789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6292982299/10000000000 : ℝ)|^71 ≤ (54997385014189/100000000000000 : ℝ)^55
        have hw : |(6292982299/10000000000 : ℝ)|=(6292982299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4529695727/10000000000 : ℝ)*x 0 + (-3251792389/10000000000 : ℝ)*x 1 + (1242923203/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4529695727/10000000000 : ℝ)^71 ≤ (8994072686737/25000000000000 : ℝ)^55 := by
    have hnat : (4529695727 : ℕ)^71*25000000000000^55 ≤ 8994072686737^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529695727 10000000000 8994072686737 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3251792389/10000000000 : ℝ)^71 ≤ (5863202706459/25000000000000 : ℝ)^55 := by
    have hnat : (3251792389 : ℕ)^71*25000000000000^55 ≤ 5863202706459^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3251792389 10000000000 5863202706459 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1242923203/2500000000 : ℝ)^71 ≤ (8114179681139/20000000000000 : ℝ)^55 := by
    have hnat : (1242923203 : ℕ)^71*20000000000000^55 ≤ 8114179681139^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242923203 2500000000 8114179681139 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4529695727/10000000000 : ℝ), (-3251792389/10000000000 : ℝ), (1242923203/2500000000 : ℝ)] ![(8994072686737/25000000000000 : ℝ), (5863202706459/25000000000000 : ℝ), (8114179681139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4529695727/10000000000 : ℝ)|^71 ≤ (8994072686737/25000000000000 : ℝ)^55
        have hw : |(4529695727/10000000000 : ℝ)|=(4529695727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3251792389/10000000000 : ℝ)|^71 ≤ (5863202706459/25000000000000 : ℝ)^55
        have hw : |(-3251792389/10000000000 : ℝ)|=(3251792389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1242923203/2500000000 : ℝ)|^71 ≤ (8114179681139/20000000000000 : ℝ)^55
        have hw : |(1242923203/2500000000 : ℝ)|=(1242923203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3273425033/5000000000 : ℝ)*x 0 + (4955051809/10000000000 : ℝ)*x 1 + (-10772153/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3273425033/5000000000 : ℝ)^71 ≤ (28939068683297/50000000000000 : ℝ)^55 := by
    have hnat : (3273425033 : ℕ)^71*50000000000000^55 ≤ 28939068683297^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3273425033 5000000000 28939068683297 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4955051809/10000000000 : ℝ)^71 ≤ (20197841187603/50000000000000 : ℝ)^55 := by
    have hnat : (4955051809 : ℕ)^71*50000000000000^55 ≤ 20197841187603^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4955051809 10000000000 20197841187603 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10772153/250000000 : ℝ)^71 ≤ (34523604909/2000000000000 : ℝ)^55 := by
    have hnat : (10772153 : ℕ)^71*2000000000000^55 ≤ 34523604909^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10772153 250000000 34523604909 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3273425033/5000000000 : ℝ), (4955051809/10000000000 : ℝ), (-10772153/250000000 : ℝ)] ![(28939068683297/50000000000000 : ℝ), (20197841187603/50000000000000 : ℝ), (34523604909/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3273425033/5000000000 : ℝ)|^71 ≤ (28939068683297/50000000000000 : ℝ)^55
        have hw : |(3273425033/5000000000 : ℝ)|=(3273425033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4955051809/10000000000 : ℝ)|^71 ≤ (20197841187603/50000000000000 : ℝ)^55
        have hw : |(4955051809/10000000000 : ℝ)|=(4955051809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10772153/250000000 : ℝ)|^71 ≤ (34523604909/2000000000000 : ℝ)^55
        have hw : |(-10772153/250000000 : ℝ)|=(10772153/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (26366899/10000000000 : ℝ)*x 0 + (273531353/500000000 : ℝ)*x 1 + (6208963049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26366899/10000000000 : ℝ)^71 ≤ (23431046953/50000000000000 : ℝ)^55 := by
    have hnat : (26366899 : ℕ)^71*50000000000000^55 ≤ 23431046953^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26366899 10000000000 23431046953 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273531353/500000000 : ℝ)^71 ≤ (11475450174843/25000000000000 : ℝ)^55 := by
    have hnat : (273531353 : ℕ)^71*25000000000000^55 ≤ 11475450174843^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273531353 500000000 11475450174843 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6208963049/10000000000 : ℝ)^71 ≤ (13512834299653/25000000000000 : ℝ)^55 := by
    have hnat : (6208963049 : ℕ)^71*25000000000000^55 ≤ 13512834299653^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6208963049 10000000000 13512834299653 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26366899/10000000000 : ℝ), (273531353/500000000 : ℝ), (6208963049/10000000000 : ℝ)] ![(23431046953/50000000000000 : ℝ), (11475450174843/25000000000000 : ℝ), (13512834299653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26366899/10000000000 : ℝ)|^71 ≤ (23431046953/50000000000000 : ℝ)^55
        have hw : |(26366899/10000000000 : ℝ)|=(26366899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273531353/500000000 : ℝ)|^71 ≤ (11475450174843/25000000000000 : ℝ)^55
        have hw : |(273531353/500000000 : ℝ)|=(273531353/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6208963049/10000000000 : ℝ)|^71 ≤ (13512834299653/25000000000000 : ℝ)^55
        have hw : |(6208963049/10000000000 : ℝ)|=(6208963049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-925629931/2500000000 : ℝ)*x 0 + (3345717963/10000000000 : ℝ)*x 1 + (1414418939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925629931/2500000000 : ℝ)^71 ≤ (2773124361583/10000000000000 : ℝ)^55 := by
    have hnat : (925629931 : ℕ)^71*10000000000000^55 ≤ 2773124361583^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925629931 2500000000 2773124361583 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3345717963/10000000000 : ℝ)^71 ≤ (2433094352969/10000000000000 : ℝ)^55 := by
    have hnat : (3345717963 : ℕ)^71*10000000000000^55 ≤ 2433094352969^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3345717963 10000000000 2433094352969 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414418939/2500000000 : ℝ)^71 ≤ (47937812835157/100000000000000 : ℝ)^55 := by
    have hnat : (1414418939 : ℕ)^71*100000000000000^55 ≤ 47937812835157^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414418939 2500000000 47937812835157 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-925629931/2500000000 : ℝ), (3345717963/10000000000 : ℝ), (1414418939/2500000000 : ℝ)] ![(2773124361583/10000000000000 : ℝ), (2433094352969/10000000000000 : ℝ), (47937812835157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-925629931/2500000000 : ℝ)|^71 ≤ (2773124361583/10000000000000 : ℝ)^55
        have hw : |(-925629931/2500000000 : ℝ)|=(925629931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3345717963/10000000000 : ℝ)|^71 ≤ (2433094352969/10000000000000 : ℝ)^55
        have hw : |(3345717963/10000000000 : ℝ)|=(3345717963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414418939/2500000000 : ℝ)|^71 ≤ (47937812835157/100000000000000 : ℝ)^55
        have hw : |(1414418939/2500000000 : ℝ)|=(1414418939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4211389223/10000000000 : ℝ)*x 0 + (-817486211/2500000000 : ℝ)*x 1 + (5259820057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211389223/10000000000 : ℝ)^71 ≤ (1309867304563/4000000000000 : ℝ)^55 := by
    have hnat : (4211389223 : ℕ)^71*4000000000000^55 ≤ 1309867304563^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211389223 10000000000 1309867304563 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (817486211/2500000000 : ℝ)^71 ≤ (5905488565141/25000000000000 : ℝ)^55 := by
    have hnat : (817486211 : ℕ)^71*25000000000000^55 ≤ 5905488565141^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817486211 2500000000 5905488565141 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259820057/10000000000 : ℝ)^71 ≤ (21815681552333/50000000000000 : ℝ)^55 := by
    have hnat : (5259820057 : ℕ)^71*50000000000000^55 ≤ 21815681552333^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259820057 10000000000 21815681552333 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211389223/10000000000 : ℝ), (-817486211/2500000000 : ℝ), (5259820057/10000000000 : ℝ)] ![(1309867304563/4000000000000 : ℝ), (5905488565141/25000000000000 : ℝ), (21815681552333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211389223/10000000000 : ℝ)|^71 ≤ (1309867304563/4000000000000 : ℝ)^55
        have hw : |(4211389223/10000000000 : ℝ)|=(4211389223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-817486211/2500000000 : ℝ)|^71 ≤ (5905488565141/25000000000000 : ℝ)^55
        have hw : |(-817486211/2500000000 : ℝ)|=(817486211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259820057/10000000000 : ℝ)|^71 ≤ (21815681552333/50000000000000 : ℝ)^55
        have hw : |(5259820057/10000000000 : ℝ)|=(5259820057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (409705039/625000000 : ℝ)*x 0 + (2396235577/5000000000 : ℝ)*x 1 + (-358640763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409705039/625000000 : ℝ)^71 ≤ (28987184232677/50000000000000 : ℝ)^55 := by
    have hnat : (409705039 : ℕ)^71*50000000000000^55 ≤ 28987184232677^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409705039 625000000 28987184232677 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2396235577/5000000000 : ℝ)^71 ≤ (4836613427921/12500000000000 : ℝ)^55 := by
    have hnat : (2396235577 : ℕ)^71*12500000000000^55 ≤ 4836613427921^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396235577 5000000000 4836613427921 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (358640763/5000000000 : ℝ)^71 ≤ (133308963539/4000000000000 : ℝ)^55 := by
    have hnat : (358640763 : ℕ)^71*4000000000000^55 ≤ 133308963539^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358640763 5000000000 133308963539 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(409705039/625000000 : ℝ), (2396235577/5000000000 : ℝ), (-358640763/5000000000 : ℝ)] ![(28987184232677/50000000000000 : ℝ), (4836613427921/12500000000000 : ℝ), (133308963539/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(409705039/625000000 : ℝ)|^71 ≤ (28987184232677/50000000000000 : ℝ)^55
        have hw : |(409705039/625000000 : ℝ)|=(409705039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2396235577/5000000000 : ℝ)|^71 ≤ (4836613427921/12500000000000 : ℝ)^55
        have hw : |(2396235577/5000000000 : ℝ)|=(2396235577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-358640763/5000000000 : ℝ)|^71 ≤ (133308963539/4000000000000 : ℝ)^55
        have hw : |(-358640763/5000000000 : ℝ)|=(358640763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310082_s1_s1_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (751763/1000000000 : ℝ)*x 0 + (856451219/1250000000 : ℝ)*x 1 + (598079263/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (751763/1000000000 : ℝ)^71 ≤ (4637399379/50000000000000 : ℝ)^55 := by
    have hnat : (751763 : ℕ)^71*50000000000000^55 ≤ 4637399379^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751763 1000000000 4637399379 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (856451219/1250000000 : ℝ)^71 ≤ (7672434894683/12500000000000 : ℝ)^55 := by
    have hnat : (856451219 : ℕ)^71*12500000000000^55 ≤ 7672434894683^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856451219 1250000000 7672434894683 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598079263/1250000000 : ℝ)^71 ≤ (38611246031071/100000000000000 : ℝ)^55 := by
    have hnat : (598079263 : ℕ)^71*100000000000000^55 ≤ 38611246031071^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598079263 1250000000 38611246031071 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(751763/1000000000 : ℝ), (856451219/1250000000 : ℝ), (598079263/1250000000 : ℝ)] ![(4637399379/50000000000000 : ℝ), (7672434894683/12500000000000 : ℝ), (38611246031071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(751763/1000000000 : ℝ)|^71 ≤ (4637399379/50000000000000 : ℝ)^55
        have hw : |(751763/1000000000 : ℝ)|=(751763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(856451219/1250000000 : ℝ)|^71 ≤ (7672434894683/12500000000000 : ℝ)^55
        have hw : |(856451219/1250000000 : ℝ)|=(856451219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598079263/1250000000 : ℝ)|^71 ≤ (38611246031071/100000000000000 : ℝ)^55
        have hw : |(598079263/1250000000 : ℝ)|=(598079263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310082_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((9663/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9663/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((17709/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(17709/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(80759/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(80759/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4891/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4891/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((49281/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(49281/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3767/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3767/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (9663/12500 : ℝ) ^ (35/8 : ℝ) ≤ (32425270186883371709/100000000000000000000 : ℝ) := by
    have hpowers : (9663/12500 : ℝ)^35 ≤ (32425270186883371709/100000000000000000000 : ℝ)^8 := by
      have hnat : (9663 : ℕ)^35*100000000000000000000^8 ≤ 32425270186883371709^8*12500^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9663 12500 32425270186883371709 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9663/12500 : ℝ)) (X := (32425270186883371709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (132425270186883371709/100000000000000000000 : ℝ) ≤ (426519652599149/400000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (132425270186883371709/100000000000000000000 : ℝ)^8 ≤ (426519652599149/400000000000000 : ℝ)^35 := by
      have hnat : (132425270186883371709 : ℕ)^8*400000000000000^35 ≤ 426519652599149^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132425270186883371709 100000000000000000000 426519652599149 400000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (426519652599149/400000000000000 : ℝ)) (X := (132425270186883371709/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (82425270186883371709/50000000000000000000 : ℝ) ≤ (2802597084190917/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (82425270186883371709/50000000000000000000 : ℝ)^8 ≤ (2802597084190917/2500000000000000 : ℝ)^35 := by
      have hnat : (82425270186883371709 : ℕ)^8*2500000000000000^35 ≤ 2802597084190917^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82425270186883371709 50000000000000000000 2802597084190917 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2802597084190917/2500000000000000 : ℝ)) (X := (82425270186883371709/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(26519652599149/309216000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(547397021784943/7730400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (9663/12500 : ℝ)) (alpha := (26519652599149/309216000000000 : ℝ)) (beta := (547397021784943/7730400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9663/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(26519652599149/309216000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(547397021784943/7730400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (17709/20000 : ℝ) ^ (35/8 : ℝ) ≤ (58727658405766882857/100000000000000000000 : ℝ) := by
    have hpowers : (17709/20000 : ℝ)^35 ≤ (58727658405766882857/100000000000000000000 : ℝ)^8 := by
      have hnat : (17709 : ℕ)^35*100000000000000000000^8 ≤ 58727658405766882857^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17709 20000 58727658405766882857 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17709/20000 : ℝ)) (X := (58727658405766882857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (158727658405766882857/100000000000000000000 : ℝ) ≤ (555691121480581/500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (158727658405766882857/100000000000000000000 : ℝ)^8 ≤ (555691121480581/500000000000000 : ℝ)^35 := by
      have hnat : (158727658405766882857 : ℕ)^8*500000000000000^35 ≤ 555691121480581^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        158727658405766882857 100000000000000000000 555691121480581 500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (555691121480581/500000000000000 : ℝ)) (X := (158727658405766882857/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (108727658405766882857/50000000000000000000 : ℝ) ≤ (11942992233188267/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (108727658405766882857/50000000000000000000 : ℝ)^8 ≤ (11942992233188267/10000000000000000 : ℝ)^35 := by
      have hnat : (108727658405766882857 : ℕ)^8*10000000000000000^35 ≤ 11942992233188267^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108727658405766882857 50000000000000000000 11942992233188267 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11942992233188267/10000000000000000 : ℝ)) (X := (108727658405766882857/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(55691121480581/442725000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(276389934525549/2951500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (17709/20000 : ℝ)) (alpha := (55691121480581/442725000000000 : ℝ)) (beta := (276389934525549/2951500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (17709/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(55691121480581/442725000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(276389934525549/2951500000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (80759/100000 : ℝ) ^ (35/8 : ℝ) ≤ (39260907174376409563/100000000000000000000 : ℝ) := by
    have hpowers : (80759/100000 : ℝ)^35 ≤ (39260907174376409563/100000000000000000000 : ℝ)^8 := by
      have hnat : (80759 : ℕ)^35*100000000000000000000^8 ≤ 39260907174376409563^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80759 100000 39260907174376409563 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80759/100000 : ℝ)) (X := (39260907174376409563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (139260907174376409563/100000000000000000000 : ℝ) ≤ (269659210667869/250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (139260907174376409563/100000000000000000000 : ℝ)^8 ≤ (269659210667869/250000000000000 : ℝ)^35 := by
      have hnat : (139260907174376409563 : ℕ)^8*250000000000000^35 ≤ 269659210667869^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        139260907174376409563 100000000000000000000 269659210667869 250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (269659210667869/250000000000000 : ℝ)) (X := (139260907174376409563/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (89260907174376409563/50000000000000000000 : ℝ) ≤ (5708203434248917/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (89260907174376409563/50000000000000000000 : ℝ)^8 ≤ (5708203434248917/5000000000000000 : ℝ)^35 := by
      have hnat : (89260907174376409563 : ℕ)^8*5000000000000000^35 ≤ 5708203434248917^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89260907174376409563 50000000000000000000 5708203434248917 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5708203434248917/5000000000000000 : ℝ)) (X := (89260907174376409563/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(19659210667869/201897500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(315019220891537/4037950000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (80759/100000 : ℝ)) (alpha := (19659210667869/201897500000000 : ℝ)) (beta := (315019220891537/4037950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (80759/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(19659210667869/201897500000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(315019220891537/4037950000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-770165611/2000000000 : ℝ)*X 0 0+(12707127/39062500 : ℝ)*X 0 1+(1401245853/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((84521829/200000000 : ℝ)*X 1 0+(-827725889/2500000000 : ℝ)*X 1 1+(2605114677/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5948214141/10000000000 : ℝ)*X 2 0+(5228925017/10000000000 : ℝ)*X 2 1+(-1066292907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((753165529/10000000000 : ℝ)*X 0 0+(5783588963/10000000000 : ℝ)*X 0 1+(174492927/312500000 : ℝ)*X 0 2+(753165529/10000000000 : ℝ)*X 1 0+(5783588963/10000000000 : ℝ)*X 1 1+(174492927/312500000 : ℝ)*X 1 2+(753165529/10000000000 : ℝ)*X 2 0+(5783588963/10000000000 : ℝ)*X 2 1+(174492927/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-27404469/78125000 : ℝ)*X 0 0+(685094343/2500000000 : ℝ)*X 0 1+(6322666999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5226523/12500000 : ℝ)*X 1 0+(-1248449191/5000000000 : ℝ)*X 1 1+(5924810353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5632880317/10000000000 : ℝ)*X 2 0+(1478482789/2500000000 : ℝ)*X 2 1+(-50150263/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((161055241/10000000000 : ℝ)*X 0 0+(371303061/500000000 : ℝ)*X 0 1+(2038963423/5000000000 : ℝ)*X 0 2+(161055241/10000000000 : ℝ)*X 1 0+(371303061/500000000 : ℝ)*X 1 1+(2038963423/5000000000 : ℝ)*X 1 2+(161055241/10000000000 : ℝ)*X 2 0+(371303061/500000000 : ℝ)*X 2 1+(2038963423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-676842567/2000000000 : ℝ)*X 0 0+(727199789/2500000000 : ℝ)*X 0 1+(6292982299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4529695727/10000000000 : ℝ)*X 1 0+(-3251792389/10000000000 : ℝ)*X 1 1+(1242923203/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3273425033/5000000000 : ℝ)*X 2 0+(4955051809/10000000000 : ℝ)*X 2 1+(-10772153/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((26366899/10000000000 : ℝ)*X 0 0+(273531353/500000000 : ℝ)*X 0 1+(6208963049/10000000000 : ℝ)*X 0 2+(26366899/10000000000 : ℝ)*X 1 0+(273531353/500000000 : ℝ)*X 1 1+(6208963049/10000000000 : ℝ)*X 1 2+(26366899/10000000000 : ℝ)*X 2 0+(273531353/500000000 : ℝ)*X 2 1+(6208963049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-925629931/2500000000 : ℝ)*X 0 0+(3345717963/10000000000 : ℝ)*X 0 1+(1414418939/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((4211389223/10000000000 : ℝ)*X 1 0+(-817486211/2500000000 : ℝ)*X 1 1+(5259820057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((409705039/625000000 : ℝ)*X 2 0+(2396235577/5000000000 : ℝ)*X 2 1+(-358640763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((751763/1000000000 : ℝ)*X 0 0+(856451219/1250000000 : ℝ)*X 0 1+(598079263/1250000000 : ℝ)*X 0 2+(751763/1000000000 : ℝ)*X 1 0+(856451219/1250000000 : ℝ)*X 1 1+(598079263/1250000000 : ℝ)*X 1 2+(751763/1000000000 : ℝ)*X 2 0+(856451219/1250000000 : ℝ)*X 2 1+(598079263/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310082_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((4891/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4891/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4128355450447012651713029072409/383879083579250000000000000000000000 : ℝ) := by norm_num
    linear_combination (846409/1000000000000 : ℝ)*(base23) + (566957/500000000000 : ℝ)*(base39) + (28511721699/125000000000 : ℝ)*(base49) + (252337729201/200000000000 : ℝ)*(base60) + (656231841861/125000000000 : ℝ)*(major_s1_0) + (656231841861/125000000000 : ℝ)*(major_s1_1) + (656231841861/125000000000 : ℝ)*(major_s1_2) + (36858201/1000000000000 : ℝ)*(sp_s1_2) + (283977/15625000000 : ℝ)*(sp_s1_6) + (362716985483/50000000000 : ℝ)*(sp_s1_7) + (906863585541/125000000000 : ℝ)*(sp_s1_8) + (3627435489859/500000000000 : ℝ)*(sp_s1_9) + (3244779026147/1000000000000 : ℝ)*(sp_s1_13) + (142243667/250000000000 : ℝ)*(sp_s1_14) + (129791888027/40000000000 : ℝ)*(f.failure) + (906863585541/125000000000 : ℝ)*(f.sum) + (47474379489278873021/119180094250000000000000000000000 : ℝ)*base63 + (212605537164729/1009487500000000000000000000 : ℝ)*base65 + (29173914548781/147575000000000000000000000 : ℝ)*base67 + (281008845418611/807590000000000000000000000 : ℝ)*base69 + (649608572371407843/26012473900000000000000000000000 : ℝ)*base70 + (92719749328661/322100000000000000000000000 : ℝ)*base73 + (414731977643397/737875000000000000000000000 : ℝ)*base75 + (6239612414597/64420000000000000000000000 : ℝ)*base77 + (172819683282162357/1901356300000000000000000000000 : ℝ)*base79 + (411/4000000000000000 : ℝ)*base87 + (411/4000000000000000 : ℝ)*base89 + (411/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((49281/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(49281/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10129821120492811821823393/950678150000000000000000000000 : ℝ) := by norm_num
    linear_combination (38817/500000000000 : ℝ)*(base31) + (1281421/500000000000 : ℝ)*(base40) + (297227/250000000000 : ℝ)*(base49) + (86207779229/40000000000 : ℝ)*(base60) + (1959071169271/250000000000 : ℝ)*(major_s1_0) + (1959071169271/250000000000 : ℝ)*(major_s1_1) + (1959071169271/250000000000 : ℝ)*(major_s1_2) + (16499637/1000000000000 : ℝ)*(sp_s1_6) + (72227293/200000000000 : ℝ)*(sp_s1_7) + (5414401555701/500000000000 : ℝ)*(sp_s1_14) + (10829164247867/1000000000000 : ℝ)*(sp_s1_15) + (10829031502519/1000000000000 : ℝ)*(sp_s1_16) + (1210846244309/250000000000 : ℝ)*(sp_s1_20) + (33186337/250000000000 : ℝ)*(sp_s1_23) + (1210850388627/250000000000 : ℝ)*(f.failure) + (10829164247867/1000000000000 : ℝ)*(f.sum) + (293263599804086577/857410750000000000000000000000 : ℝ)*base63 + (1661598239143/29050000000000000000000000 : ℝ)*base64 + (315103182232817/885450000000000000000000000 : ℝ)*base66 + (1125886235491/2905000000000000000000000 : ℝ)*base68 + (846738565434977039/1122840600000000000000000000000 : ℝ)*base71 + (1126125484940807/1932600000000000000000000000 : ℝ)*base72 + (628892282317783/1475750000000000000000000000 : ℝ)*base74 + (39513032492687/386520000000000000000000000 : ℝ)*base77 + (903595326040231289/11408137800000000000000000000000 : ℝ)*base78 + (28211/25000000000000000 : ℝ)*base87 + (28211/25000000000000000 : ℝ)*base89 + (28211/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3767/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3767/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (570361132387838234284584246723/153551633431700000000000000000000000 : ℝ) := by norm_num
    linear_combination (330459/500000000000 : ℝ)*(base40) + (609203/1000000000000 : ℝ)*(base49) + (46919574447/31250000000 : ℝ)*(base60) + (7812558892931/1000000000000 : ℝ)*(major_s1_0) + (7812558892931/1000000000000 : ℝ)*(major_s1_1) + (7812558892931/1000000000000 : ℝ)*(major_s1_2) + (17429029/200000000000 : ℝ)*(sp_s1_0) + (46521383/200000000000 : ℝ)*(sp_s1_1) + (663199/40000000000 : ℝ)*(sp_s1_13) + (7463103/500000000000 : ℝ)*(sp_s1_16) + (5398146065759/500000000000 : ℝ)*(sp_s1_21) + (10796146669747/1000000000000 : ℝ)*(sp_s1_22) + (10796364350457/1000000000000 : ℝ)*(sp_s1_23) + (603590086383/125000000000 : ℝ)*(sp_s1_27) + (2414368635519/500000000000 : ℝ)*(f.failure) + (5398189638331/500000000000 : ℝ)*(f.sum) + (34846594298556021479/238360188500000000000000000000000 : ℝ)*base63 + (2307097851154143/4037950000000000000000000000 : ℝ)*base64 + (33398665767913/55340625000000000000000000 : ℝ)*base66 + (24795474967871/80759000000000000000000000 : ℝ)*base69 + (155972109938875277399/624299373600000000000000000000000 : ℝ)*base70 + (2734784015356867/7730400000000000000000000000 : ℝ)*base72 + (1553529142207969/2951500000000000000000000000 : ℝ)*base74 + (145904896770937/309216000000000000000000000 : ℝ)*base76 + (26242934505199607389/45632551200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (24433/50000000000000000 : ℝ)*base86 + (24433/50000000000000000 : ℝ)*base88 + (24433/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((9663/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9663/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((17709/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(17709/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(80759/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(80759/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4891/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4891/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((49281/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(49281/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3767/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3767/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310082_s1 p hpa hpb X hX hprev0

#print axioms solution

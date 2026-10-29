-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308063_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:39:33.732994+00:00
-- url     : https://prove2.me/submissions/989cc56a-fa47-4120-aa7e-96313b61f263

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
theorem collision_support_c308063_s3_s3_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-939187043/10000000000 : ℝ)*x 0 + (1117340639/2000000000 : ℝ)*x 1 + (5739576359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939187043/10000000000 : ℝ)^69 ≤ (4598746989757/100000000000000 : ℝ)^53 := by
    have hnat : (939187043 : ℕ)^69*100000000000000^53 ≤ 4598746989757^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939187043 10000000000 4598746989757 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117340639/2000000000 : ℝ)^69 ≤ (9372494833821/20000000000000 : ℝ)^53 := by
    have hnat : (1117340639 : ℕ)^69*20000000000000^53 ≤ 9372494833821^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117340639 2000000000 9372494833821 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5739576359/10000000000 : ℝ)^69 ≤ (48538778823411/100000000000000 : ℝ)^53 := by
    have hnat : (5739576359 : ℕ)^69*100000000000000^53 ≤ 48538778823411^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5739576359 10000000000 48538778823411 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-939187043/10000000000 : ℝ), (1117340639/2000000000 : ℝ), (5739576359/10000000000 : ℝ)] ![(4598746989757/100000000000000 : ℝ), (9372494833821/20000000000000 : ℝ), (48538778823411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-939187043/10000000000 : ℝ)|^69 ≤ (4598746989757/100000000000000 : ℝ)^53
        have hw : |(-939187043/10000000000 : ℝ)|=(939187043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1117340639/2000000000 : ℝ)|^69 ≤ (9372494833821/20000000000000 : ℝ)^53
        have hw : |(1117340639/2000000000 : ℝ)|=(1117340639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5739576359/10000000000 : ℝ)|^69 ≤ (48538778823411/100000000000000 : ℝ)^53
        have hw : |(5739576359/10000000000 : ℝ)|=(5739576359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5586969087/10000000000 : ℝ)*x 0 + (-943841877/10000000000 : ℝ)*x 1 + (5736615231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5586969087/10000000000 : ℝ)^69 ≤ (23432688932821/50000000000000 : ℝ)^53 := by
    have hnat : (5586969087 : ℕ)^69*50000000000000^53 ≤ 23432688932821^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586969087 10000000000 23432688932821 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943841877/10000000000 : ℝ)^69 ≤ (578555299309/12500000000000 : ℝ)^53 := by
    have hnat : (943841877 : ℕ)^69*12500000000000^53 ≤ 578555299309^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943841877 10000000000 578555299309 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5736615231/10000000000 : ℝ)^69 ≤ (48506179725357/100000000000000 : ℝ)^53 := by
    have hnat : (5736615231 : ℕ)^69*100000000000000^53 ≤ 48506179725357^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5736615231 10000000000 48506179725357 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5586969087/10000000000 : ℝ), (-943841877/10000000000 : ℝ), (5736615231/10000000000 : ℝ)] ![(23432688932821/50000000000000 : ℝ), (578555299309/12500000000000 : ℝ), (48506179725357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5586969087/10000000000 : ℝ)|^69 ≤ (23432688932821/50000000000000 : ℝ)^53
        have hw : |(5586969087/10000000000 : ℝ)|=(5586969087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-943841877/10000000000 : ℝ)|^69 ≤ (578555299309/12500000000000 : ℝ)^53
        have hw : |(-943841877/10000000000 : ℝ)|=(943841877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5736615231/10000000000 : ℝ)|^69 ≤ (48506179725357/100000000000000 : ℝ)^53
        have hw : |(5736615231/10000000000 : ℝ)|=(5736615231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5646589283/10000000000 : ℝ)*x 0 + (1428492539/2500000000 : ℝ)*x 1 + (-880055391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5646589283/10000000000 : ℝ)^69 ≤ (47517516201171/100000000000000 : ℝ)^53 := by
    have hnat : (5646589283 : ℕ)^69*100000000000000^53 ≤ 47517516201171^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5646589283 10000000000 47517516201171 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1428492539/2500000000 : ℝ)^69 ≤ (6032130984809/12500000000000 : ℝ)^53 := by
    have hnat : (1428492539 : ℕ)^69*12500000000000^53 ≤ 6032130984809^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428492539 2500000000 6032130984809 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880055391/10000000000 : ℝ)^69 ≤ (4225435915337/100000000000000 : ℝ)^53 := by
    have hnat : (880055391 : ℕ)^69*100000000000000^53 ≤ 4225435915337^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880055391 10000000000 4225435915337 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5646589283/10000000000 : ℝ), (1428492539/2500000000 : ℝ), (-880055391/10000000000 : ℝ)] ![(47517516201171/100000000000000 : ℝ), (6032130984809/12500000000000 : ℝ), (4225435915337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5646589283/10000000000 : ℝ)|^69 ≤ (47517516201171/100000000000000 : ℝ)^53
        have hw : |(5646589283/10000000000 : ℝ)|=(5646589283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1428492539/2500000000 : ℝ)|^69 ≤ (6032130984809/12500000000000 : ℝ)^53
        have hw : |(1428492539/2500000000 : ℝ)|=(1428492539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-880055391/10000000000 : ℝ)|^69 ≤ (4225435915337/100000000000000 : ℝ)^53
        have hw : |(-880055391/10000000000 : ℝ)|=(880055391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (89744251/200000000 : ℝ)*x 0 + (4328877077/10000000000 : ℝ)*x 1 + (2041189913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89744251/200000000 : ℝ)^69 ≤ (17615013917079/50000000000000 : ℝ)^53 := by
    have hnat : (89744251 : ℕ)^69*50000000000000^53 ≤ 17615013917079^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89744251 200000000 17615013917079 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4328877077/10000000000 : ℝ)^69 ≤ (33620312465777/100000000000000 : ℝ)^53 := by
    have hnat : (4328877077 : ℕ)^69*100000000000000^53 ≤ 33620312465777^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328877077 10000000000 33620312465777 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2041189913/5000000000 : ℝ)^69 ≤ (31149659684091/100000000000000 : ℝ)^53 := by
    have hnat : (2041189913 : ℕ)^69*100000000000000^53 ≤ 31149659684091^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041189913 5000000000 31149659684091 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(89744251/200000000 : ℝ), (4328877077/10000000000 : ℝ), (2041189913/5000000000 : ℝ)] ![(17615013917079/50000000000000 : ℝ), (33620312465777/100000000000000 : ℝ), (31149659684091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(89744251/200000000 : ℝ)|^69 ≤ (17615013917079/50000000000000 : ℝ)^53
        have hw : |(89744251/200000000 : ℝ)|=(89744251/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4328877077/10000000000 : ℝ)|^69 ≤ (33620312465777/100000000000000 : ℝ)^53
        have hw : |(4328877077/10000000000 : ℝ)|=(4328877077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2041189913/5000000000 : ℝ)|^69 ≤ (31149659684091/100000000000000 : ℝ)^53
        have hw : |(2041189913/5000000000 : ℝ)|=(2041189913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-965591893/10000000000 : ℝ)*x 0 + (188674179/500000000 : ℝ)*x 1 + (7361718853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965591893/10000000000 : ℝ)^69 ≤ (953556006137/20000000000000 : ℝ)^53 := by
    have hnat : (965591893 : ℕ)^69*20000000000000^53 ≤ 953556006137^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965591893 10000000000 953556006137 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188674179/500000000 : ℝ)^69 ≤ (14058423083017/50000000000000 : ℝ)^53 := by
    have hnat : (188674179 : ℕ)^69*50000000000000^53 ≤ 14058423083017^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188674179 500000000 14058423083017 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7361718853/10000000000 : ℝ)^69 ≤ (67115373781703/100000000000000 : ℝ)^53 := by
    have hnat : (7361718853 : ℕ)^69*100000000000000^53 ≤ 67115373781703^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7361718853 10000000000 67115373781703 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-965591893/10000000000 : ℝ), (188674179/500000000 : ℝ), (7361718853/10000000000 : ℝ)] ![(953556006137/20000000000000 : ℝ), (14058423083017/50000000000000 : ℝ), (67115373781703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-965591893/10000000000 : ℝ)|^69 ≤ (953556006137/20000000000000 : ℝ)^53
        have hw : |(-965591893/10000000000 : ℝ)|=(965591893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(188674179/500000000 : ℝ)|^69 ≤ (14058423083017/50000000000000 : ℝ)^53
        have hw : |(188674179/500000000 : ℝ)|=(188674179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7361718853/10000000000 : ℝ)|^69 ≤ (67115373781703/100000000000000 : ℝ)^53
        have hw : |(7361718853/10000000000 : ℝ)|=(7361718853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (105171897/250000000 : ℝ)*x 0 + (-179153277/10000000000 : ℝ)*x 1 + (7358400749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105171897/250000000 : ℝ)^69 ≤ (16196012478451/50000000000000 : ℝ)^53 := by
    have hnat : (105171897 : ℕ)^69*50000000000000^53 ≤ 16196012478451^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105171897 250000000 16196012478451 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179153277/10000000000 : ℝ)^69 ≤ (531981318021/100000000000000 : ℝ)^53 := by
    have hnat : (179153277 : ℕ)^69*100000000000000^53 ≤ 531981318021^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179153277 10000000000 531981318021 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7358400749/10000000000 : ℝ)^69 ≤ (1676899842869/2500000000000 : ℝ)^53 := by
    have hnat : (7358400749 : ℕ)^69*2500000000000^53 ≤ 1676899842869^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7358400749 10000000000 1676899842869 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105171897/250000000 : ℝ), (-179153277/10000000000 : ℝ), (7358400749/10000000000 : ℝ)] ![(16196012478451/50000000000000 : ℝ), (531981318021/100000000000000 : ℝ), (1676899842869/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105171897/250000000 : ℝ)|^69 ≤ (16196012478451/50000000000000 : ℝ)^53
        have hw : |(105171897/250000000 : ℝ)|=(105171897/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179153277/10000000000 : ℝ)|^69 ≤ (531981318021/100000000000000 : ℝ)^53
        have hw : |(-179153277/10000000000 : ℝ)|=(179153277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7358400749/10000000000 : ℝ)|^69 ≤ (1676899842869/2500000000000 : ℝ)^53
        have hw : |(7358400749/10000000000 : ℝ)|=(7358400749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1965107851/5000000000 : ℝ)*x 0 + (3811776441/5000000000 : ℝ)*x 1 + (-54754163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1965107851/5000000000 : ℝ)^69 ≤ (29646678943209/100000000000000 : ℝ)^53 := by
    have hnat : (1965107851 : ℕ)^69*100000000000000^53 ≤ 29646678943209^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965107851 5000000000 29646678943209 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3811776441/5000000000 : ℝ)^69 ≤ (70239643372501/100000000000000 : ℝ)^53 := by
    have hnat : (3811776441 : ℕ)^69*100000000000000^53 ≤ 70239643372501^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3811776441 5000000000 70239643372501 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54754163/10000000000 : ℝ)^69 ≤ (7104854161/6250000000000 : ℝ)^53 := by
    have hnat : (54754163 : ℕ)^69*6250000000000^53 ≤ 7104854161^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54754163 10000000000 7104854161 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1965107851/5000000000 : ℝ), (3811776441/5000000000 : ℝ), (-54754163/10000000000 : ℝ)] ![(29646678943209/100000000000000 : ℝ), (70239643372501/100000000000000 : ℝ), (7104854161/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1965107851/5000000000 : ℝ)|^69 ≤ (29646678943209/100000000000000 : ℝ)^53
        have hw : |(1965107851/5000000000 : ℝ)|=(1965107851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3811776441/5000000000 : ℝ)|^69 ≤ (70239643372501/100000000000000 : ℝ)^53
        have hw : |(3811776441/5000000000 : ℝ)|=(3811776441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54754163/10000000000 : ℝ)|^69 ≤ (7104854161/6250000000000 : ℝ)^53
        have hw : |(-54754163/10000000000 : ℝ)|=(54754163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (983796229/2500000000 : ℝ)*x 0 + (6736584023/10000000000 : ℝ)*x 1 + (110768403/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983796229/2500000000 : ℝ)^69 ≤ (5939097667913/20000000000000 : ℝ)^53 := by
    have hnat : (983796229 : ℕ)^69*20000000000000^53 ≤ 5939097667913^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983796229 2500000000 5939097667913 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6736584023/10000000000 : ℝ)^69 ≤ (29896335319817/50000000000000 : ℝ)^53 := by
    have hnat : (6736584023 : ℕ)^69*50000000000000^53 ≤ 29896335319817^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6736584023 10000000000 29896335319817 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110768403/625000000 : ℝ)^69 ≤ (10511841000763/100000000000000 : ℝ)^53 := by
    have hnat : (110768403 : ℕ)^69*100000000000000^53 ≤ 10511841000763^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110768403 625000000 10511841000763 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(983796229/2500000000 : ℝ), (6736584023/10000000000 : ℝ), (110768403/625000000 : ℝ)] ![(5939097667913/20000000000000 : ℝ), (29896335319817/50000000000000 : ℝ), (10511841000763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(983796229/2500000000 : ℝ)|^69 ≤ (5939097667913/20000000000000 : ℝ)^53
        have hw : |(983796229/2500000000 : ℝ)|=(983796229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6736584023/10000000000 : ℝ)|^69 ≤ (29896335319817/50000000000000 : ℝ)^53
        have hw : |(6736584023/10000000000 : ℝ)|=(6736584023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110768403/625000000 : ℝ)|^69 ≤ (10511841000763/100000000000000 : ℝ)^53
        have hw : |(110768403/625000000 : ℝ)|=(110768403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-9356301/625000000 : ℝ)*x 0 + (4127678183/10000000000 : ℝ)*x 1 + (1486867049/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9356301/625000000 : ℝ)^69 ≤ (105266080671/25000000000000 : ℝ)^53 := by
    have hnat : (9356301 : ℕ)^69*25000000000000^53 ≤ 105266080671^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9356301 625000000 105266080671 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127678183/10000000000 : ℝ)^69 ≤ (31600393854993/100000000000000 : ℝ)^53 := by
    have hnat : (4127678183 : ℕ)^69*100000000000000^53 ≤ 31600393854993^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127678183 10000000000 31600393854993 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1486867049/2000000000 : ℝ)^69 ≤ (33989270903207/50000000000000 : ℝ)^53 := by
    have hnat : (1486867049 : ℕ)^69*50000000000000^53 ≤ 33989270903207^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486867049 2000000000 33989270903207 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9356301/625000000 : ℝ), (4127678183/10000000000 : ℝ), (1486867049/2000000000 : ℝ)] ![(105266080671/25000000000000 : ℝ), (31600393854993/100000000000000 : ℝ), (33989270903207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9356301/625000000 : ℝ)|^69 ≤ (105266080671/25000000000000 : ℝ)^53
        have hw : |(-9356301/625000000 : ℝ)|=(9356301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127678183/10000000000 : ℝ)|^69 ≤ (31600393854993/100000000000000 : ℝ)^53
        have hw : |(4127678183/10000000000 : ℝ)|=(4127678183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1486867049/2000000000 : ℝ)|^69 ≤ (33989270903207/50000000000000 : ℝ)^53
        have hw : |(1486867049/2000000000 : ℝ)|=(1486867049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (147030891/400000000 : ℝ)*x 0 + (-196872341/2000000000 : ℝ)*x 1 + (7430970671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (147030891/400000000 : ℝ)^69 ≤ (27172717897849/100000000000000 : ℝ)^53 := by
    have hnat : (147030891 : ℕ)^69*100000000000000^53 ≤ 27172717897849^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147030891 400000000 27172717897849 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196872341/2000000000 : ℝ)^69 ≤ (4888790363887/100000000000000 : ℝ)^53 := by
    have hnat : (196872341 : ℕ)^69*100000000000000^53 ≤ 4888790363887^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196872341 2000000000 4888790363887 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7430970671/10000000000 : ℝ)^69 ≤ (13587698346227/20000000000000 : ℝ)^53 := by
    have hnat : (7430970671 : ℕ)^69*20000000000000^53 ≤ 13587698346227^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7430970671 10000000000 13587698346227 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(147030891/400000000 : ℝ), (-196872341/2000000000 : ℝ), (7430970671/10000000000 : ℝ)] ![(27172717897849/100000000000000 : ℝ), (4888790363887/100000000000000 : ℝ), (13587698346227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(147030891/400000000 : ℝ)|^69 ≤ (27172717897849/100000000000000 : ℝ)^53
        have hw : |(147030891/400000000 : ℝ)|=(147030891/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196872341/2000000000 : ℝ)|^69 ≤ (4888790363887/100000000000000 : ℝ)^53
        have hw : |(-196872341/2000000000 : ℝ)|=(196872341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7430970671/10000000000 : ℝ)|^69 ≤ (13587698346227/20000000000000 : ℝ)^53
        have hw : |(7430970671/10000000000 : ℝ)|=(7430970671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7330950511/10000000000 : ℝ)*x 0 + (427223807/1000000000 : ℝ)*x 1 + (-2119287/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7330950511/10000000000 : ℝ)^69 ≤ (66750413364259/100000000000000 : ℝ)^53 := by
    have hnat : (7330950511 : ℕ)^69*100000000000000^53 ≤ 66750413364259^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7330950511 10000000000 66750413364259 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427223807/1000000000 : ℝ)^69 ≤ (33048762560077/100000000000000 : ℝ)^53 := by
    have hnat : (427223807 : ℕ)^69*100000000000000^53 ≤ 33048762560077^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427223807 1000000000 33048762560077 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119287/250000000 : ℝ)^69 ≤ (200824055161/100000000000000 : ℝ)^53 := by
    have hnat : (2119287 : ℕ)^69*100000000000000^53 ≤ 200824055161^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119287 250000000 200824055161 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7330950511/10000000000 : ℝ), (427223807/1000000000 : ℝ), (-2119287/250000000 : ℝ)] ![(66750413364259/100000000000000 : ℝ), (33048762560077/100000000000000 : ℝ), (200824055161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7330950511/10000000000 : ℝ)|^69 ≤ (66750413364259/100000000000000 : ℝ)^53
        have hw : |(7330950511/10000000000 : ℝ)|=(7330950511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(427223807/1000000000 : ℝ)|^69 ≤ (33048762560077/100000000000000 : ℝ)^53
        have hw : |(427223807/1000000000 : ℝ)|=(427223807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2119287/250000000 : ℝ)|^69 ≤ (200824055161/100000000000000 : ℝ)^53
        have hw : |(-2119287/250000000 : ℝ)|=(2119287/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1474041109/2000000000 : ℝ)*x 0 + (12673091/40000000 : ℝ)*x 1 + (439126659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1474041109/2000000000 : ℝ)^69 ≤ (4201007517969/6250000000000 : ℝ)^53 := by
    have hnat : (1474041109 : ℕ)^69*6250000000000^53 ≤ 4201007517969^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1474041109 2000000000 4201007517969 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12673091/40000000 : ℝ)^69 ≤ (1119689203947/5000000000000 : ℝ)^53 := by
    have hnat : (12673091 : ℕ)^69*5000000000000^53 ≤ 1119689203947^53*40000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12673091 40000000 1119689203947 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439126659/2500000000 : ℝ)^69 ≤ (10390095617277/100000000000000 : ℝ)^53 := by
    have hnat : (439126659 : ℕ)^69*100000000000000^53 ≤ 10390095617277^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439126659 2500000000 10390095617277 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1474041109/2000000000 : ℝ), (12673091/40000000 : ℝ), (439126659/2500000000 : ℝ)] ![(4201007517969/6250000000000 : ℝ), (1119689203947/5000000000000 : ℝ), (10390095617277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1474041109/2000000000 : ℝ)|^69 ≤ (4201007517969/6250000000000 : ℝ)^53
        have hw : |(1474041109/2000000000 : ℝ)|=(1474041109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12673091/40000000 : ℝ)|^69 ≤ (1119689203947/5000000000000 : ℝ)^53
        have hw : |(12673091/40000000 : ℝ)|=(12673091/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(439126659/2500000000 : ℝ)|^69 ≤ (10390095617277/100000000000000 : ℝ)^53
        have hw : |(439126659/2500000000 : ℝ)|=(439126659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-119844743/10000000000 : ℝ)*x 0 + (1363986007/2000000000 : ℝ)*x 1 + (1211176347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119844743/10000000000 : ℝ)^69 ≤ (157597542887/50000000000000 : ℝ)^53 := by
    have hnat : (119844743 : ℕ)^69*50000000000000^53 ≤ 157597542887^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119844743 10000000000 157597542887 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363986007/2000000000 : ℝ)^69 ≤ (60757552703633/100000000000000 : ℝ)^53 := by
    have hnat : (1363986007 : ℕ)^69*100000000000000^53 ≤ 60757552703633^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363986007 2000000000 60757552703633 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1211176347/2500000000 : ℝ)^69 ≤ (9731813049889/25000000000000 : ℝ)^53 := by
    have hnat : (1211176347 : ℕ)^69*25000000000000^53 ≤ 9731813049889^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211176347 2500000000 9731813049889 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-119844743/10000000000 : ℝ), (1363986007/2000000000 : ℝ), (1211176347/2500000000 : ℝ)] ![(157597542887/50000000000000 : ℝ), (60757552703633/100000000000000 : ℝ), (9731813049889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-119844743/10000000000 : ℝ)|^69 ≤ (157597542887/50000000000000 : ℝ)^53
        have hw : |(-119844743/10000000000 : ℝ)|=(119844743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363986007/2000000000 : ℝ)|^69 ≤ (60757552703633/100000000000000 : ℝ)^53
        have hw : |(1363986007/2000000000 : ℝ)|=(1363986007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1211176347/2500000000 : ℝ)|^69 ≤ (9731813049889/25000000000000 : ℝ)^53
        have hw : |(1211176347/2500000000 : ℝ)|=(1211176347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (731038933/1000000000 : ℝ)*x 0 + (-18423399/2500000000 : ℝ)*x 1 + (859945219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (731038933/1000000000 : ℝ)^69 ≤ (66506783271579/100000000000000 : ℝ)^53 := by
    have hnat : (731038933 : ℕ)^69*100000000000000^53 ≤ 66506783271579^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731038933 1000000000 66506783271579 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18423399/2500000000 : ℝ)^69 ≤ (167353560461/100000000000000 : ℝ)^53 := by
    have hnat : (18423399 : ℕ)^69*100000000000000^53 ≤ 167353560461^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18423399 2500000000 167353560461 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (859945219/2000000000 : ℝ)^69 ≤ (33325863157511/100000000000000 : ℝ)^53 := by
    have hnat : (859945219 : ℕ)^69*100000000000000^53 ≤ 33325863157511^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859945219 2000000000 33325863157511 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(731038933/1000000000 : ℝ), (-18423399/2500000000 : ℝ), (859945219/2000000000 : ℝ)] ![(66506783271579/100000000000000 : ℝ), (167353560461/100000000000000 : ℝ), (33325863157511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(731038933/1000000000 : ℝ)|^69 ≤ (66506783271579/100000000000000 : ℝ)^53
        have hw : |(731038933/1000000000 : ℝ)|=(731038933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18423399/2500000000 : ℝ)|^69 ≤ (167353560461/100000000000000 : ℝ)^53
        have hw : |(-18423399/2500000000 : ℝ)|=(18423399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(859945219/2000000000 : ℝ)|^69 ≤ (33325863157511/100000000000000 : ℝ)^53
        have hw : |(859945219/2000000000 : ℝ)|=(859945219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (362649489/1000000000 : ℝ)*x 0 + (7506435001/10000000000 : ℝ)*x 1 + (-36709439/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (362649489/1000000000 : ℝ)^69 ≤ (13349716368379/50000000000000 : ℝ)^53 := by
    have hnat : (362649489 : ℕ)^69*50000000000000^53 ≤ 13349716368379^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362649489 1000000000 13349716368379 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7506435001/10000000000 : ℝ)^69 ≤ (68838090694593/100000000000000 : ℝ)^53 := by
    have hnat : (7506435001 : ℕ)^69*100000000000000^53 ≤ 68838090694593^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7506435001 10000000000 68838090694593 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36709439/400000000 : ℝ)^69 ≤ (278904784307/6250000000000 : ℝ)^53 := by
    have hnat : (36709439 : ℕ)^69*6250000000000^53 ≤ 278904784307^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36709439 400000000 278904784307 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(362649489/1000000000 : ℝ), (7506435001/10000000000 : ℝ), (-36709439/400000000 : ℝ)] ![(13349716368379/50000000000000 : ℝ), (68838090694593/100000000000000 : ℝ), (278904784307/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(362649489/1000000000 : ℝ)|^69 ≤ (13349716368379/50000000000000 : ℝ)^53
        have hw : |(362649489/1000000000 : ℝ)|=(362649489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7506435001/10000000000 : ℝ)|^69 ≤ (68838090694593/100000000000000 : ℝ)^53
        have hw : |(7506435001/10000000000 : ℝ)|=(7506435001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-36709439/400000000 : ℝ)|^69 ≤ (278904784307/6250000000000 : ℝ)^53
        have hw : |(-36709439/400000000 : ℝ)|=(36709439/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308063_s3_s3_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3756837713/5000000000 : ℝ)*x 0 + (2605414411/10000000000 : ℝ)*x 1 + (543536899/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3756837713/5000000000 : ℝ)^69 ≤ (13784909356507/20000000000000 : ℝ)^53 := by
    have hnat : (3756837713 : ℕ)^69*20000000000000^53 ≤ 13784909356507^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3756837713 5000000000 13784909356507 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2605414411/10000000000 : ℝ)^69 ≤ (8679760449871/50000000000000 : ℝ)^53 := by
    have hnat : (2605414411 : ℕ)^69*50000000000000^53 ≤ 8679760449871^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605414411 10000000000 8679760449871 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543536899/2500000000 : ℝ)^69 ≤ (13715932294323/100000000000000 : ℝ)^53 := by
    have hnat : (543536899 : ℕ)^69*100000000000000^53 ≤ 13715932294323^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543536899 2500000000 13715932294323 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3756837713/5000000000 : ℝ), (2605414411/10000000000 : ℝ), (543536899/2500000000 : ℝ)] ![(13784909356507/20000000000000 : ℝ), (8679760449871/50000000000000 : ℝ), (13715932294323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3756837713/5000000000 : ℝ)|^69 ≤ (13784909356507/20000000000000 : ℝ)^53
        have hw : |(3756837713/5000000000 : ℝ)|=(3756837713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2605414411/10000000000 : ℝ)|^69 ≤ (8679760449871/50000000000000 : ℝ)^53
        have hw : |(2605414411/10000000000 : ℝ)|=(2605414411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543536899/2500000000 : ℝ)|^69 ≤ (13715932294323/100000000000000 : ℝ)^53
        have hw : |(543536899/2500000000 : ℝ)|=(543536899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308063_s3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((74101/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74101/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37149/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37149/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35777/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35777/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((63593/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63593/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64277/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64277/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61727/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (74101/100000 : ℝ) ^ (17/4 : ℝ) ≤ (27973853276867660683/100000000000000000000 : ℝ) := by
    have hpowers : (74101/100000 : ℝ)^17 ≤ (27973853276867660683/100000000000000000000 : ℝ)^4 := by
      have hnat : (74101 : ℕ)^17*100000000000000000000^4 ≤ 27973853276867660683^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74101 100000 27973853276867660683 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74101/100000 : ℝ)) (X := (27973853276867660683/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner0a : (127973853276867660683/100000000000000000000 : ℝ) ≤ (10597538407842651/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (127973853276867660683/100000000000000000000 : ℝ)^4 ≤ (10597538407842651/10000000000000000 : ℝ)^17 := by
      have hnat : (127973853276867660683 : ℕ)^4*10000000000000000^17 ≤ 10597538407842651^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127973853276867660683 100000000000000000000 10597538407842651 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10597538407842651/10000000000000000 : ℝ)) (X := (127973853276867660683/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner0b : (77973853276867660683/50000000000000000000 : ℝ) ≤ (11102143122032211/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (77973853276867660683/50000000000000000000 : ℝ)^4 ≤ (11102143122032211/10000000000000000 : ℝ)^17 := by
      have hnat : (77973853276867660683 : ℕ)^4*10000000000000000^17 ≤ 11102143122032211^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77973853276867660683 50000000000000000000 11102143122032211 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11102143122032211/10000000000000000 : ℝ)) (X := (77973853276867660683/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(597538407842651/7410100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12615117854739/185252500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (74101/100000 : ℝ)) (alpha := (597538407842651/7410100000000000 : ℝ)) (beta := (12615117854739/185252500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (74101/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(597538407842651/7410100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12615117854739/185252500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (37149/50000 : ℝ) ^ (17/4 : ℝ) ≤ (7072822884213506239/25000000000000000000 : ℝ) := by
    have hpowers : (37149/50000 : ℝ)^17 ≤ (7072822884213506239/25000000000000000000 : ℝ)^4 := by
      have hnat : (37149 : ℕ)^17*25000000000000000000^4 ≤ 7072822884213506239^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37149 50000 7072822884213506239 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37149/50000 : ℝ)) (X := (7072822884213506239/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner1a : (32072822884213506239/25000000000000000000 : ℝ) ≤ (10603717755107869/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (32072822884213506239/25000000000000000000 : ℝ)^4 ≤ (10603717755107869/10000000000000000 : ℝ)^17 := by
      have hnat : (32072822884213506239 : ℕ)^4*10000000000000000^17 ≤ 10603717755107869^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32072822884213506239 25000000000000000000 10603717755107869 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10603717755107869/10000000000000000 : ℝ)) (X := (32072822884213506239/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner1b : (19572822884213506239/12500000000000000000 : ℝ) ≤ (11112761379116037/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (19572822884213506239/12500000000000000000 : ℝ)^4 ≤ (11112761379116037/10000000000000000 : ℝ)^17 := by
      have hnat : (19572822884213506239 : ℕ)^4*10000000000000000^17 ≤ 11112761379116037^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19572822884213506239 12500000000000000000 11112761379116037 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11112761379116037/10000000000000000 : ℝ)) (X := (19572822884213506239/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(201239251702623/2476600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(63630453001021/928725000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (37149/50000 : ℝ)) (alpha := (201239251702623/2476600000000000 : ℝ)) (beta := (63630453001021/928725000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (37149/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(201239251702623/2476600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(63630453001021/928725000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (35777/50000 : ℝ) ^ (17/4 : ℝ) ≤ (24109829863601350993/100000000000000000000 : ℝ) := by
    have hpowers : (35777/50000 : ℝ)^17 ≤ (24109829863601350993/100000000000000000000 : ℝ)^4 := by
      have hnat : (35777 : ℕ)^17*100000000000000000000^4 ≤ 24109829863601350993^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35777 50000 24109829863601350993 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35777/50000 : ℝ)) (X := (24109829863601350993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner2a : (124109829863601350993/100000000000000000000 : ℝ) ≤ (10521363917198129/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (124109829863601350993/100000000000000000000 : ℝ)^4 ≤ (10521363917198129/10000000000000000 : ℝ)^17 := by
      have hnat : (124109829863601350993 : ℕ)^4*10000000000000000^17 ≤ 10521363917198129^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        124109829863601350993 100000000000000000000 10521363917198129 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10521363917198129/10000000000000000 : ℝ)) (X := (124109829863601350993/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner2b : (74109829863601350993/50000000000000000000 : ℝ) ≤ (10970164304234779/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (74109829863601350993/50000000000000000000 : ℝ)^4 ≤ (10970164304234779/10000000000000000 : ℝ)^17 := by
      have hnat : (74109829863601350993 : ℕ)^4*10000000000000000^17 ≤ 10970164304234779^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74109829863601350993 50000000000000000000 10970164304234779 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10970164304234779/10000000000000000 : ℝ)) (X := (74109829863601350993/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(521363917198129/7155400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8976007740733/143108000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (35777/50000 : ℝ)) (alpha := (521363917198129/7155400000000000 : ℝ)) (beta := (8976007740733/143108000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (35777/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(521363917198129/7155400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8976007740733/143108000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-939187043/10000000000 : ℝ)*X 0 0+(1117340639/2000000000 : ℝ)*X 0 1+(5739576359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((5586969087/10000000000 : ℝ)*X 1 0+(-943841877/10000000000 : ℝ)*X 1 1+(5736615231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((5646589283/10000000000 : ℝ)*X 2 0+(1428492539/2500000000 : ℝ)*X 2 1+(-880055391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((89744251/200000000 : ℝ)*X 0 0+(4328877077/10000000000 : ℝ)*X 0 1+(2041189913/5000000000 : ℝ)*X 0 2+(89744251/200000000 : ℝ)*X 1 0+(4328877077/10000000000 : ℝ)*X 1 1+(2041189913/5000000000 : ℝ)*X 1 2+(89744251/200000000 : ℝ)*X 2 0+(4328877077/10000000000 : ℝ)*X 2 1+(2041189913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-965591893/10000000000 : ℝ)*X 0 0+(188674179/500000000 : ℝ)*X 0 1+(7361718853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((105171897/250000000 : ℝ)*X 1 0+(-179153277/10000000000 : ℝ)*X 1 1+(7358400749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((1965107851/5000000000 : ℝ)*X 2 0+(3811776441/5000000000 : ℝ)*X 2 1+(-54754163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((983796229/2500000000 : ℝ)*X 0 0+(6736584023/10000000000 : ℝ)*X 0 1+(110768403/625000000 : ℝ)*X 0 2+(983796229/2500000000 : ℝ)*X 1 0+(6736584023/10000000000 : ℝ)*X 1 1+(110768403/625000000 : ℝ)*X 1 2+(983796229/2500000000 : ℝ)*X 2 0+(6736584023/10000000000 : ℝ)*X 2 1+(110768403/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-9356301/625000000 : ℝ)*X 0 0+(4127678183/10000000000 : ℝ)*X 0 1+(1486867049/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((147030891/400000000 : ℝ)*X 1 0+(-196872341/2000000000 : ℝ)*X 1 1+(7430970671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((7330950511/10000000000 : ℝ)*X 2 0+(427223807/1000000000 : ℝ)*X 2 1+(-2119287/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((1474041109/2000000000 : ℝ)*X 0 0+(12673091/40000000 : ℝ)*X 0 1+(439126659/2500000000 : ℝ)*X 0 2+(1474041109/2000000000 : ℝ)*X 1 0+(12673091/40000000 : ℝ)*X 1 1+(439126659/2500000000 : ℝ)*X 1 2+(1474041109/2000000000 : ℝ)*X 2 0+(12673091/40000000 : ℝ)*X 2 1+(439126659/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-119844743/10000000000 : ℝ)*X 0 0+(1363986007/2000000000 : ℝ)*X 0 1+(1211176347/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((731038933/1000000000 : ℝ)*X 1 0+(-18423399/2500000000 : ℝ)*X 1 1+(859945219/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((362649489/1000000000 : ℝ)*X 2 0+(7506435001/10000000000 : ℝ)*X 2 1+(-36709439/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((3756837713/5000000000 : ℝ)*X 0 0+(2605414411/10000000000 : ℝ)*X 0 1+(543536899/2500000000 : ℝ)*X 0 2+(3756837713/5000000000 : ℝ)*X 1 0+(2605414411/10000000000 : ℝ)*X 1 1+(543536899/2500000000 : ℝ)*X 1 2+(3756837713/5000000000 : ℝ)*X 2 0+(2605414411/10000000000 : ℝ)*X 2 1+(543536899/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308063_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((63593/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63593/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (213429633085705223377629/63289513000000000000000000000 : ℝ) := by norm_num
    linear_combination (40575804459/100000000000 : ℝ)*(base7) + (25697/125000000000 : ℝ)*(base50) + (51048723769/500000000000 : ℝ)*(base60) + (473149030503/200000000000 : ℝ)*(major_s3_0) + (473149030503/200000000000 : ℝ)*(major_s3_1) + (473149030503/200000000000 : ℝ)*(major_s3_2) + (351793/125000000000 : ℝ)*(sp_s3_0) + (1291417/1000000000000 : ℝ)*(sp_s3_6) + (118904381829/40000000000 : ℝ)*(sp_s3_7) + (1486316726719/500000000000 : ℝ)*(sp_s3_8) + (2972633393733/1000000000000 : ℝ)*(sp_s3_9) + (11971122871/6250000000 : ℝ)*(sp_s3_13) + (21093369/1000000000000 : ℝ)*(sp_s3_14) + (11941/200000000000 : ℝ)*(sp_s3_23) + (1509622906187/1000000000000 : ℝ)*(f.failure) + (1486316726719/500000000000 : ℝ)*(f.sum) + (577614389942311517/1265790260000000000000000000000 : ℝ)*base63 + (131917105907309/715540000000000000000000000 : ℝ)*base64 + (1767968178671/61915000000000000000000000 : ℝ)*base66 + (829386842243487/1431080000000000000000000000 : ℝ)*base69 + (14259141396998890573/26511114770000000000000000000000 : ℝ)*base70 + (41612781517039/185252500000000000000000000 : ℝ)*base73 + (236590742268337/495320000000000000000000000 : ℝ)*base75 + (217658928910253/1482020000000000000000000000 : ℝ)*base77 + (1528331815446254691/4587963415000000000000000000000 : ℝ)*base78 + (29043/100000000000000000 : ℝ)*base86 + (29043/100000000000000000 : ℝ)*base88 + (29043/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64277/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64277/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3717374539104183711069502554037/234490810140650000000000000000000000 : ℝ) := by norm_num
    linear_combination (448548947917/1000000000000 : ℝ)*(base7) + (1435079/1000000000000 : ℝ)*(base49) + (35142372047/15625000000 : ℝ)*(major_s3_0) + (35142372047/15625000000 : ℝ)*(major_s3_1) + (35142372047/15625000000 : ℝ)*(major_s3_2) + (4318591/1000000000000 : ℝ)*(sp_s3_1) + (19491/25000000000 : ℝ)*(sp_s3_2) + (319127/4000000000 : ℝ)*(sp_s3_8) + (2787504006063/1000000000000 : ℝ)*(sp_s3_14) + (557484075643/200000000000 : ℝ)*(sp_s3_15) + (696875924729/250000000000 : ℝ)*(sp_s3_16) + (75346998819/40000000000 : ℝ)*(sp_s3_20) + (236247/500000000000 : ℝ)*(sp_s3_21) + (35565403/500000000000 : ℝ)*(sp_s3_27) + (358799288341/250000000000 : ℝ)*(f.failure) + (2787504478557/1000000000000 : ℝ)*(f.sum) + (634907203294267943/3164475650000000000000000000000 : ℝ)*base63 + (29683103325427/71554000000000000000000000 : ℝ)*base64 + (1078168612700999/1857450000000000000000000000 : ℝ)*base66 + (543897931202903/1788850000000000000000000000 : ℝ)*base69 + (214393701420242567/33138893462500000000000000000000 : ℝ)*base71 + (42605091035359/185252500000000000000000000 : ℝ)*base73 + (256219475115791/619150000000000000000000000 : ℝ)*base75 + (178807614426431/926262500000000000000000000 : ℝ)*base77 + (9943875115417094381/34409725612500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (6451/25000000000000000 : ℝ)*base87 + (6451/25000000000000000 : ℝ)*base89 + (6451/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61727/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (81496097501711700964520985703/6699737432590000000000000000000000 : ℝ) := by norm_num
    linear_combination (440033401429/1000000000000 : ℝ)*(base7) + (72179338601/500000000000 : ℝ)*(base40) + (179901/125000000000 : ℝ)*(base49) + (2155634601253/1000000000000 : ℝ)*(major_s3_0) + (2155634601253/1000000000000 : ℝ)*(major_s3_1) + (2155634601253/1000000000000 : ℝ)*(major_s3_2) + (11901487/1000000000000 : ℝ)*(sp_s3_1) + (2356853/100000000000 : ℝ)*(sp_s3_2) + (90259073/1000000000000 : ℝ)*(sp_s3_9) + (9001827/1000000000000 : ℝ)*(sp_s3_20) + (533086260507/200000000000 : ℝ)*(sp_s3_21) + (333177425131/125000000000 : ℝ)*(sp_s3_22) + (666329368733/250000000000 : ℝ)*(sp_s3_23) + (363114425677/200000000000 : ℝ)*(sp_s3_27) + (1375547728783/1000000000000 : ℝ)*(f.failure) + (533086260507/200000000000 : ℝ)*(f.sum) + (155651742943176117/904135900000000000000000000000 : ℝ)*base62 + (8907143677717/20444000000000000000000000 : ℝ)*base64 + (36834860588951/132675000000000000000000000 : ℝ)*base66 + (499385143148389/1022200000000000000000000000 : ℝ)*base68 + (269924350364509383/2367063818750000000000000000000 : ℝ)*base71 + (439022946315521/741010000000000000000000000 : ℝ)*base72 + (183150019173063/353800000000000000000000000 : ℝ)*base74 + (1771287390006127/7410100000000000000000000000 : ℝ)*base76 + (3396127647743099407/19662700350000000000000000000000 : ℝ)*base78 + (12713/100000000000000000 : ℝ)*base87 + (12713/100000000000000000 : ℝ)*base89 + (12713/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((74101/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74101/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37149/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37149/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35777/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35777/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((63593/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63593/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64277/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(64277/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61727/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308063_s3 p hpa hpb X hX hprev2

#print axioms solution

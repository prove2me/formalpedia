-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308060_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:38:06.703005+00:00
-- url     : https://prove2.me/submissions/bb583b75-7813-46c3-8373-0a0dd4e644d7

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
theorem collision_support_c308060_s3_s3_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4719429629/10000000000 : ℝ)*x 0 + (1446154267/2500000000 : ℝ)*x 1 + (266071643/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4719429629/10000000000 : ℝ)^69 ≤ (18810964797903/50000000000000 : ℝ)^53 := by
    have hnat : (4719429629 : ℕ)^69*50000000000000^53 ≤ 18810964797903^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4719429629 10000000000 18810964797903 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1446154267/2500000000 : ℝ)^69 ≤ (49035257538851/100000000000000 : ℝ)^53 := by
    have hnat : (1446154267 : ℕ)^69*100000000000000^53 ≤ 49035257538851^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446154267 2500000000 49035257538851 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266071643/1250000000 : ℝ)^69 ≤ (6671406424789/50000000000000 : ℝ)^53 := by
    have hnat : (266071643 : ℕ)^69*50000000000000^53 ≤ 6671406424789^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266071643 1250000000 6671406424789 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4719429629/10000000000 : ℝ), (1446154267/2500000000 : ℝ), (266071643/1250000000 : ℝ)] ![(18810964797903/50000000000000 : ℝ), (49035257538851/100000000000000 : ℝ), (6671406424789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4719429629/10000000000 : ℝ)|^69 ≤ (18810964797903/50000000000000 : ℝ)^53
        have hw : |(4719429629/10000000000 : ℝ)|=(4719429629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1446154267/2500000000 : ℝ)|^69 ≤ (49035257538851/100000000000000 : ℝ)^53
        have hw : |(1446154267/2500000000 : ℝ)|=(1446154267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(266071643/1250000000 : ℝ)|^69 ≤ (6671406424789/50000000000000 : ℝ)^53
        have hw : |(266071643/1250000000 : ℝ)|=(266071643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6742151871/10000000000 : ℝ)*x 0 + (1095201237/2500000000 : ℝ)*x 1 + (-287894579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6742151871/10000000000 : ℝ)^69 ≤ (59857016850759/100000000000000 : ℝ)^53 := by
    have hnat : (6742151871 : ℕ)^69*100000000000000^53 ≤ 59857016850759^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6742151871 10000000000 59857016850759 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095201237/2500000000 : ℝ)^69 ≤ (17073154996863/50000000000000 : ℝ)^53 := by
    have hnat : (1095201237 : ℕ)^69*50000000000000^53 ≤ 17073154996863^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095201237 2500000000 17073154996863 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287894579/2500000000 : ℝ)^69 ≤ (1499168286241/25000000000000 : ℝ)^53 := by
    have hnat : (287894579 : ℕ)^69*25000000000000^53 ≤ 1499168286241^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287894579 2500000000 1499168286241 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6742151871/10000000000 : ℝ), (1095201237/2500000000 : ℝ), (-287894579/2500000000 : ℝ)] ![(59857016850759/100000000000000 : ℝ), (17073154996863/50000000000000 : ℝ), (1499168286241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6742151871/10000000000 : ℝ)|^69 ≤ (59857016850759/100000000000000 : ℝ)^53
        have hw : |(6742151871/10000000000 : ℝ)|=(6742151871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095201237/2500000000 : ℝ)|^69 ≤ (17073154996863/50000000000000 : ℝ)^53
        have hw : |(1095201237/2500000000 : ℝ)|=(1095201237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-287894579/2500000000 : ℝ)|^69 ≤ (1499168286241/25000000000000 : ℝ)^53
        have hw : |(-287894579/2500000000 : ℝ)|=(287894579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2068529801/10000000000 : ℝ)*x 0 + (3765048521/10000000000 : ℝ)*x 1 + (-3338715143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068529801/10000000000 : ℝ)^69 ≤ (12854912135169/100000000000000 : ℝ)^53 := by
    have hnat : (2068529801 : ℕ)^69*100000000000000^53 ≤ 12854912135169^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068529801 10000000000 12854912135169 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3765048521/10000000000 : ℝ)^69 ≤ (5607009777707/20000000000000 : ℝ)^53 := by
    have hnat : (3765048521 : ℕ)^69*20000000000000^53 ≤ 5607009777707^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3765048521 10000000000 5607009777707 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3338715143/5000000000 : ℝ)^69 ≤ (2955501948151/5000000000000 : ℝ)^53 := by
    have hnat : (3338715143 : ℕ)^69*5000000000000^53 ≤ 2955501948151^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3338715143 5000000000 2955501948151 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2068529801/10000000000 : ℝ), (3765048521/10000000000 : ℝ), (-3338715143/5000000000 : ℝ)] ![(12854912135169/100000000000000 : ℝ), (5607009777707/20000000000000 : ℝ), (2955501948151/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2068529801/10000000000 : ℝ)|^69 ≤ (12854912135169/100000000000000 : ℝ)^53
        have hw : |(-2068529801/10000000000 : ℝ)|=(2068529801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3765048521/10000000000 : ℝ)|^69 ≤ (5607009777707/20000000000000 : ℝ)^53
        have hw : |(3765048521/10000000000 : ℝ)|=(3765048521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3338715143/5000000000 : ℝ)|^69 ≤ (2955501948151/5000000000000 : ℝ)^53
        have hw : |(-3338715143/5000000000 : ℝ)|=(3338715143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4072986833/10000000000 : ℝ)*x 0 + (-82504173/500000000 : ℝ)*x 1 + (-6699583509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4072986833/10000000000 : ℝ)^69 ≤ (31056384486133/100000000000000 : ℝ)^53 := by
    have hnat : (4072986833 : ℕ)^69*100000000000000^53 ≤ 31056384486133^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4072986833 10000000000 31056384486133 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82504173/500000000 : ℝ)^69 ≤ (1197267775051/12500000000000 : ℝ)^53 := by
    have hnat : (82504173 : ℕ)^69*12500000000000^53 ≤ 1197267775051^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82504173 500000000 1197267775051 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6699583509/10000000000 : ℝ)^69 ≤ (59365473304397/100000000000000 : ℝ)^53 := by
    have hnat : (6699583509 : ℕ)^69*100000000000000^53 ≤ 59365473304397^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6699583509 10000000000 59365473304397 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4072986833/10000000000 : ℝ), (-82504173/500000000 : ℝ), (-6699583509/10000000000 : ℝ)] ![(31056384486133/100000000000000 : ℝ), (1197267775051/12500000000000 : ℝ), (59365473304397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4072986833/10000000000 : ℝ)|^69 ≤ (31056384486133/100000000000000 : ℝ)^53
        have hw : |(4072986833/10000000000 : ℝ)|=(4072986833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-82504173/500000000 : ℝ)|^69 ≤ (1197267775051/12500000000000 : ℝ)^53
        have hw : |(-82504173/500000000 : ℝ)|=(82504173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6699583509/10000000000 : ℝ)|^69 ≤ (59365473304397/100000000000000 : ℝ)^53
        have hw : |(-6699583509/10000000000 : ℝ)|=(6699583509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4334849767/10000000000 : ℝ)*x 0 + (1358679153/2000000000 : ℝ)*x 1 + (283185927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334849767/10000000000 : ℝ)^69 ≤ (16840357843207/50000000000000 : ℝ)^53 := by
    have hnat : (4334849767 : ℕ)^69*50000000000000^53 ≤ 16840357843207^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334849767 10000000000 16840357843207 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358679153/2000000000 : ℝ)^69 ≤ (3022499085999/5000000000000 : ℝ)^53 := by
    have hnat : (1358679153 : ℕ)^69*5000000000000^53 ≤ 3022499085999^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358679153 2000000000 3022499085999 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283185927/2500000000 : ℝ)^69 ≤ (5869302573811/100000000000000 : ℝ)^53 := by
    have hnat : (283185927 : ℕ)^69*100000000000000^53 ≤ 5869302573811^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283185927 2500000000 5869302573811 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334849767/10000000000 : ℝ), (1358679153/2000000000 : ℝ), (283185927/2500000000 : ℝ)] ![(16840357843207/50000000000000 : ℝ), (3022499085999/5000000000000 : ℝ), (5869302573811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334849767/10000000000 : ℝ)|^69 ≤ (16840357843207/50000000000000 : ℝ)^53
        have hw : |(4334849767/10000000000 : ℝ)|=(4334849767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358679153/2000000000 : ℝ)|^69 ≤ (3022499085999/5000000000000 : ℝ)^53
        have hw : |(1358679153/2000000000 : ℝ)|=(1358679153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283185927/2500000000 : ℝ)|^69 ≤ (5869302573811/100000000000000 : ℝ)^53
        have hw : |(283185927/2500000000 : ℝ)|=(283185927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (126350053/200000000 : ℝ)*x 0 + (5286514099/10000000000 : ℝ)*x 1 + (-375184961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126350053/200000000 : ℝ)^69 ≤ (54996206403307/100000000000000 : ℝ)^53 := by
    have hnat : (126350053 : ℕ)^69*100000000000000^53 ≤ 54996206403307^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126350053 200000000 54996206403307 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5286514099/10000000000 : ℝ)^69 ≤ (1744447415613/4000000000000 : ℝ)^53 := by
    have hnat : (5286514099 : ℕ)^69*4000000000000^53 ≤ 1744447415613^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286514099 10000000000 1744447415613 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375184961/10000000000 : ℝ)^69 ≤ (1392608190873/100000000000000 : ℝ)^53 := by
    have hnat : (375184961 : ℕ)^69*100000000000000^53 ≤ 1392608190873^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375184961 10000000000 1392608190873 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(126350053/200000000 : ℝ), (5286514099/10000000000 : ℝ), (-375184961/10000000000 : ℝ)] ![(54996206403307/100000000000000 : ℝ), (1744447415613/4000000000000 : ℝ), (1392608190873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(126350053/200000000 : ℝ)|^69 ≤ (54996206403307/100000000000000 : ℝ)^53
        have hw : |(126350053/200000000 : ℝ)|=(126350053/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5286514099/10000000000 : ℝ)|^69 ≤ (1744447415613/4000000000000 : ℝ)^53
        have hw : |(5286514099/10000000000 : ℝ)|=(5286514099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-375184961/10000000000 : ℝ)|^69 ≤ (1392608190873/100000000000000 : ℝ)^53
        have hw : |(-375184961/10000000000 : ℝ)|=(375184961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1365618163/10000000000 : ℝ)*x 0 + (2147642859/5000000000 : ℝ)*x 1 + (-668802163/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1365618163/10000000000 : ℝ)^69 ≤ (299472264651/4000000000000 : ℝ)^53 := by
    have hnat : (1365618163 : ℕ)^69*4000000000000^53 ≤ 299472264651^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365618163 10000000000 299472264651 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147642859/5000000000 : ℝ)^69 ≤ (16640532200373/50000000000000 : ℝ)^53 := by
    have hnat : (2147642859 : ℕ)^69*50000000000000^53 ≤ 16640532200373^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147642859 5000000000 16640532200373 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (668802163/1000000000 : ℝ)^69 ≤ (14808032241543/25000000000000 : ℝ)^53 := by
    have hnat : (668802163 : ℕ)^69*25000000000000^53 ≤ 14808032241543^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668802163 1000000000 14808032241543 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1365618163/10000000000 : ℝ), (2147642859/5000000000 : ℝ), (-668802163/1000000000 : ℝ)] ![(299472264651/4000000000000 : ℝ), (16640532200373/50000000000000 : ℝ), (14808032241543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1365618163/10000000000 : ℝ)|^69 ≤ (299472264651/4000000000000 : ℝ)^53
        have hw : |(-1365618163/10000000000 : ℝ)|=(1365618163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2147642859/5000000000 : ℝ)|^69 ≤ (16640532200373/50000000000000 : ℝ)^53
        have hw : |(2147642859/5000000000 : ℝ)|=(2147642859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-668802163/1000000000 : ℝ)|^69 ≤ (14808032241543/25000000000000 : ℝ)^53
        have hw : |(-668802163/1000000000 : ℝ)|=(668802163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (403544463/1000000000 : ℝ)*x 0 + (-366206583/2000000000 : ℝ)*x 1 + (-6611217959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403544463/1000000000 : ℝ)^69 ≤ (1534211429423/5000000000000 : ℝ)^53 := by
    have hnat : (403544463 : ℕ)^69*5000000000000^53 ≤ 1534211429423^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403544463 1000000000 1534211429423 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366206583/2000000000 : ℝ)^69 ≤ (10967656935059/100000000000000 : ℝ)^53 := by
    have hnat : (366206583 : ℕ)^69*100000000000000^53 ≤ 10967656935059^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366206583 2000000000 10967656935059 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6611217959/10000000000 : ℝ)^69 ≤ (11669622892801/20000000000000 : ℝ)^53 := by
    have hnat : (6611217959 : ℕ)^69*20000000000000^53 ≤ 11669622892801^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6611217959 10000000000 11669622892801 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(403544463/1000000000 : ℝ), (-366206583/2000000000 : ℝ), (-6611217959/10000000000 : ℝ)] ![(1534211429423/5000000000000 : ℝ), (10967656935059/100000000000000 : ℝ), (11669622892801/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(403544463/1000000000 : ℝ)|^69 ≤ (1534211429423/5000000000000 : ℝ)^53
        have hw : |(403544463/1000000000 : ℝ)|=(403544463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366206583/2000000000 : ℝ)|^69 ≤ (10967656935059/100000000000000 : ℝ)^53
        have hw : |(-366206583/2000000000 : ℝ)|=(366206583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6611217959/10000000000 : ℝ)|^69 ≤ (11669622892801/20000000000000 : ℝ)^53
        have hw : |(-6611217959/10000000000 : ℝ)|=(6611217959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (566230741/1000000000 : ℝ)*x 0 + (5492643279/10000000000 : ℝ)*x 1 + (1221110441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (566230741/1000000000 : ℝ)^69 ≤ (23844895920047/50000000000000 : ℝ)^53 := by
    have hnat : (566230741 : ℕ)^69*50000000000000^53 ≤ 23844895920047^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566230741 1000000000 23844895920047 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492643279/10000000000 : ℝ)^69 ≤ (45837912838593/100000000000000 : ℝ)^53 := by
    have hnat : (5492643279 : ℕ)^69*100000000000000^53 ≤ 45837912838593^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492643279 10000000000 45837912838593 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1221110441/10000000000 : ℝ)^69 ≤ (1618073826229/25000000000000 : ℝ)^53 := by
    have hnat : (1221110441 : ℕ)^69*25000000000000^53 ≤ 1618073826229^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221110441 10000000000 1618073826229 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(566230741/1000000000 : ℝ), (5492643279/10000000000 : ℝ), (1221110441/10000000000 : ℝ)] ![(23844895920047/50000000000000 : ℝ), (45837912838593/100000000000000 : ℝ), (1618073826229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(566230741/1000000000 : ℝ)|^69 ≤ (23844895920047/50000000000000 : ℝ)^53
        have hw : |(566230741/1000000000 : ℝ)|=(566230741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492643279/10000000000 : ℝ)|^69 ≤ (45837912838593/100000000000000 : ℝ)^53
        have hw : |(5492643279/10000000000 : ℝ)|=(5492643279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1221110441/10000000000 : ℝ)|^69 ≤ (1618073826229/25000000000000 : ℝ)^53
        have hw : |(1221110441/10000000000 : ℝ)|=(1221110441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3865266697/5000000000 : ℝ)*x 0 + (3677573153/10000000000 : ℝ)*x 1 + (-352577957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3865266697/5000000000 : ℝ)^69 ≤ (2861023101129/4000000000000 : ℝ)^53 := by
    have hnat : (3865266697 : ℕ)^69*4000000000000^53 ≤ 2861023101129^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3865266697 5000000000 2861023101129 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3677573153/10000000000 : ℝ)^69 ≤ (3398756364083/12500000000000 : ℝ)^53 := by
    have hnat : (3677573153 : ℕ)^69*12500000000000^53 ≤ 3398756364083^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3677573153 10000000000 3398756364083 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352577957/10000000000 : ℝ)^69 ≤ (321092886781/25000000000000 : ℝ)^53 := by
    have hnat : (352577957 : ℕ)^69*25000000000000^53 ≤ 321092886781^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352577957 10000000000 321092886781 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3865266697/5000000000 : ℝ), (3677573153/10000000000 : ℝ), (-352577957/10000000000 : ℝ)] ![(2861023101129/4000000000000 : ℝ), (3398756364083/12500000000000 : ℝ), (321092886781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3865266697/5000000000 : ℝ)|^69 ≤ (2861023101129/4000000000000 : ℝ)^53
        have hw : |(3865266697/5000000000 : ℝ)|=(3865266697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3677573153/10000000000 : ℝ)|^69 ≤ (3398756364083/12500000000000 : ℝ)^53
        have hw : |(3677573153/10000000000 : ℝ)|=(3677573153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352577957/10000000000 : ℝ)|^69 ≤ (321092886781/25000000000000 : ℝ)^53
        have hw : |(-352577957/10000000000 : ℝ)|=(352577957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-110365139/1000000000 : ℝ)*x 0 + (641755683/1250000000 : ℝ)*x 1 + (-6082268831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110365139/1000000000 : ℝ)^69 ≤ (5673819446401/100000000000000 : ℝ)^53 := by
    have hnat : (110365139 : ℕ)^69*100000000000000^53 ≤ 5673819446401^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110365139 1000000000 5673819446401 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641755683/1250000000 : ℝ)^69 ≤ (41980859008229/100000000000000 : ℝ)^53 := by
    have hnat : (641755683 : ℕ)^69*100000000000000^53 ≤ 41980859008229^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641755683 1250000000 41980859008229 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6082268831/10000000000 : ℝ)^69 ≤ (26172660765313/50000000000000 : ℝ)^53 := by
    have hnat : (6082268831 : ℕ)^69*50000000000000^53 ≤ 26172660765313^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6082268831 10000000000 26172660765313 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110365139/1000000000 : ℝ), (641755683/1250000000 : ℝ), (-6082268831/10000000000 : ℝ)] ![(5673819446401/100000000000000 : ℝ), (41980859008229/100000000000000 : ℝ), (26172660765313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110365139/1000000000 : ℝ)|^69 ≤ (5673819446401/100000000000000 : ℝ)^53
        have hw : |(-110365139/1000000000 : ℝ)|=(110365139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641755683/1250000000 : ℝ)|^69 ≤ (41980859008229/100000000000000 : ℝ)^53
        have hw : |(641755683/1250000000 : ℝ)|=(641755683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6082268831/10000000000 : ℝ)|^69 ≤ (26172660765313/50000000000000 : ℝ)^53
        have hw : |(-6082268831/10000000000 : ℝ)|=(6082268831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (44237549/78125000 : ℝ)*x 0 + (-415997859/2500000000 : ℝ)*x 1 + (-5194516793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44237549/78125000 : ℝ)^69 ≤ (23845437928107/50000000000000 : ℝ)^53 := by
    have hnat : (44237549 : ℕ)^69*50000000000000^53 ≤ 23845437928107^53*78125000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44237549 78125000 23845437928107 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415997859/2500000000 : ℝ)^69 ≤ (4841689014411/50000000000000 : ℝ)^53 := by
    have hnat : (415997859 : ℕ)^69*50000000000000^53 ≤ 4841689014411^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415997859 2500000000 4841689014411 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194516793/10000000000 : ℝ)^69 ≤ (42625746099261/100000000000000 : ℝ)^53 := by
    have hnat : (5194516793 : ℕ)^69*100000000000000^53 ≤ 42625746099261^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194516793 10000000000 42625746099261 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44237549/78125000 : ℝ), (-415997859/2500000000 : ℝ), (-5194516793/10000000000 : ℝ)] ![(23845437928107/50000000000000 : ℝ), (4841689014411/50000000000000 : ℝ), (42625746099261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44237549/78125000 : ℝ)|^69 ≤ (23845437928107/50000000000000 : ℝ)^53
        have hw : |(44237549/78125000 : ℝ)|=(44237549/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415997859/2500000000 : ℝ)|^69 ≤ (4841689014411/50000000000000 : ℝ)^53
        have hw : |(-415997859/2500000000 : ℝ)|=(415997859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5194516793/10000000000 : ℝ)|^69 ≤ (42625746099261/100000000000000 : ℝ)^53
        have hw : |(-5194516793/10000000000 : ℝ)|=(5194516793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4191204169/10000000000 : ℝ)*x 0 + (1578688697/2500000000 : ℝ)*x 1 + (515432279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191204169/10000000000 : ℝ)^69 ≤ (644700326359/2000000000000 : ℝ)^53 := by
    have hnat : (4191204169 : ℕ)^69*2000000000000^53 ≤ 644700326359^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191204169 10000000000 644700326359 2000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1578688697/2500000000 : ℝ)^69 ≤ (54965065807131/100000000000000 : ℝ)^53 := by
    have hnat : (1578688697 : ℕ)^69*100000000000000^53 ≤ 54965065807131^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578688697 2500000000 54965065807131 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515432279/2500000000 : ℝ)^69 ≤ (63999589307/500000000000 : ℝ)^53 := by
    have hnat : (515432279 : ℕ)^69*500000000000^53 ≤ 63999589307^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515432279 2500000000 63999589307 500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191204169/10000000000 : ℝ), (1578688697/2500000000 : ℝ), (515432279/2500000000 : ℝ)] ![(644700326359/2000000000000 : ℝ), (54965065807131/100000000000000 : ℝ), (63999589307/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191204169/10000000000 : ℝ)|^69 ≤ (644700326359/2000000000000 : ℝ)^53
        have hw : |(4191204169/10000000000 : ℝ)|=(4191204169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1578688697/2500000000 : ℝ)|^69 ≤ (54965065807131/100000000000000 : ℝ)^53
        have hw : |(1578688697/2500000000 : ℝ)|=(1578688697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515432279/2500000000 : ℝ)|^69 ≤ (63999589307/500000000000 : ℝ)^53
        have hw : |(515432279/2500000000 : ℝ)|=(515432279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308060_s3_s3_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7956990381/10000000000 : ℝ)*x 0 + (3356606831/10000000000 : ℝ)*x 1 + (-103974641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7956990381/10000000000 : ℝ)^69 ≤ (7426534734421/10000000000000 : ℝ)^53 := by
    have hnat : (7956990381 : ℕ)^69*10000000000000^53 ≤ 7426534734421^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7956990381 10000000000 7426534734421 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3356606831/10000000000 : ℝ)^69 ≤ (24142158056349/100000000000000 : ℝ)^53 := by
    have hnat : (3356606831 : ℕ)^69*100000000000000^53 ≤ 24142158056349^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3356606831 10000000000 24142158056349 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103974641/2500000000 : ℝ)^69 ≤ (1592494580333/100000000000000 : ℝ)^53 := by
    have hnat : (103974641 : ℕ)^69*100000000000000^53 ≤ 1592494580333^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103974641 2500000000 1592494580333 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7956990381/10000000000 : ℝ), (3356606831/10000000000 : ℝ), (-103974641/2500000000 : ℝ)] ![(7426534734421/10000000000000 : ℝ), (24142158056349/100000000000000 : ℝ), (1592494580333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7956990381/10000000000 : ℝ)|^69 ≤ (7426534734421/10000000000000 : ℝ)^53
        have hw : |(7956990381/10000000000 : ℝ)|=(7956990381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3356606831/10000000000 : ℝ)|^69 ≤ (24142158056349/100000000000000 : ℝ)^53
        have hw : |(3356606831/10000000000 : ℝ)|=(3356606831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103974641/2500000000 : ℝ)|^69 ≤ (1592494580333/100000000000000 : ℝ)^53
        have hw : |(-103974641/2500000000 : ℝ)|=(103974641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308060_s3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((71997/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71997/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73427/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(73427/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5999/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5999/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22581/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22581/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49211/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(49211/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-33241/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-33241/100000 : ℝ)*X 1 2) := by
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
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (71997/100000 : ℝ) ^ (17/4 : ℝ) ≤ (1546914175599770233/6250000000000000000 : ℝ) := by
    have hpowers : (71997/100000 : ℝ)^17 ≤ (1546914175599770233/6250000000000000000 : ℝ)^4 := by
      have hnat : (71997 : ℕ)^17*6250000000000000000^4 ≤ 1546914175599770233^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71997 100000 1546914175599770233 6250000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71997/100000 : ℝ)) (X := (1546914175599770233/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner0a : (7796914175599770233/6250000000000000000 : ℝ) ≤ (2633530179383553/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (7796914175599770233/6250000000000000000 : ℝ)^4 ≤ (2633530179383553/2500000000000000 : ℝ)^17 := by
      have hnat : (7796914175599770233 : ℕ)^4*2500000000000000^17 ≤ 2633530179383553^17*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7796914175599770233 6250000000000000000 2633530179383553 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2633530179383553/2500000000000000 : ℝ)) (X := (7796914175599770233/6250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner0b : (4671914175599770233/3125000000000000000 : ℝ) ≤ (1374051198345341/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (4671914175599770233/3125000000000000000 : ℝ)^4 ≤ (1374051198345341/1250000000000000 : ℝ)^17 := by
      have hnat : (4671914175599770233 : ℕ)^4*1250000000000000^17 ≤ 1374051198345341^17*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4671914175599770233 3125000000000000000 1374051198345341 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1374051198345341/1250000000000000 : ℝ)) (X := (4671914175599770233/3125000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(133530179383553/1799925000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(114572217307129/1799925000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (71997/100000 : ℝ)) (alpha := (133530179383553/1799925000000000 : ℝ)) (beta := (114572217307129/1799925000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (71997/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(133530179383553/1799925000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(114572217307129/1799925000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (73427/100000 : ℝ) ^ (17/4 : ℝ) ≤ (2690835103851665071/10000000000000000000 : ℝ) := by
    have hpowers : (73427/100000 : ℝ)^17 ≤ (2690835103851665071/10000000000000000000 : ℝ)^4 := by
      have hnat : (73427 : ℕ)^17*10000000000000000000^4 ≤ 2690835103851665071^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73427 100000 2690835103851665071 10000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73427/100000 : ℝ)) (X := (2690835103851665071/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner1a : (12690835103851665071/10000000000000000000 : ℝ) ≤ (10576710946604231/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (12690835103851665071/10000000000000000000 : ℝ)^4 ≤ (10576710946604231/10000000000000000 : ℝ)^17 := by
      have hnat : (12690835103851665071 : ℕ)^4*10000000000000000^17 ≤ 10576710946604231^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12690835103851665071 10000000000000000000 10576710946604231 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10576710946604231/10000000000000000 : ℝ)) (X := (12690835103851665071/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner1b : (7690835103851665071/5000000000000000000 : ℝ) ≤ (5533129398814371/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (7690835103851665071/5000000000000000000 : ℝ)^4 ≤ (5533129398814371/5000000000000000 : ℝ)^17 := by
      have hnat : (7690835103851665071 : ℕ)^4*5000000000000000^17 ≤ 5533129398814371^17*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7690835103851665071 5000000000000000000 5533129398814371 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5533129398814371/5000000000000000 : ℝ)) (X := (7690835103851665071/5000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(576710946604231/7342700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(489547851024511/7342700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (73427/100000 : ℝ)) (alpha := (576710946604231/7342700000000000 : ℝ)) (beta := (489547851024511/7342700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (73427/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(576710946604231/7342700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(489547851024511/7342700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (5999/10000 : ℝ) ^ (17/4 : ℝ) ≤ (113981708710029127/1000000000000000000 : ℝ) := by
    have hpowers : (5999/10000 : ℝ)^17 ≤ (113981708710029127/1000000000000000000 : ℝ)^4 := by
      have hnat : (5999 : ℕ)^17*1000000000000000000^4 ≤ 113981708710029127^4*10000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5999 10000 113981708710029127 1000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5999/10000 : ℝ)) (X := (113981708710029127/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner2a : (1113981708710029127/1000000000000000000 : ℝ) ≤ (10257230893683521/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (1113981708710029127/1000000000000000000 : ℝ)^4 ≤ (10257230893683521/10000000000000000 : ℝ)^17 := by
      have hnat : (1113981708710029127 : ℕ)^4*10000000000000000^17 ≤ 10257230893683521^17*1000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1113981708710029127 1000000000000000000 10257230893683521 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10257230893683521/10000000000000000 : ℝ)) (X := (1113981708710029127/1000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner2b : (613981708710029127/500000000000000000 : ℝ) ≤ (10495057124373353/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (613981708710029127/500000000000000000 : ℝ)^4 ≤ (10495057124373353/10000000000000000 : ℝ)^17 := by
      have hnat : (613981708710029127 : ℕ)^4*10000000000000000^17 ≤ 10495057124373353^17*500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        613981708710029127 500000000000000000 10495057124373353 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10495057124373353/10000000000000000 : ℝ)) (X := (613981708710029127/500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(257230893683521/5999000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(29728278836229/749875000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (5999/10000 : ℝ)) (alpha := (257230893683521/5999000000000000 : ℝ)) (beta := (29728278836229/749875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5999/10000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(257230893683521/5999000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(29728278836229/749875000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_2 : ((4719429629/10000000000 : ℝ)*X 2 0+(1446154267/2500000000 : ℝ)*X 2 1+(266071643/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((6742151871/10000000000 : ℝ)*X 0 0+(1095201237/2500000000 : ℝ)*X 0 1+(-287894579/2500000000 : ℝ)*X 0 2+(6742151871/10000000000 : ℝ)*X 1 0+(1095201237/2500000000 : ℝ)*X 1 1+(-287894579/2500000000 : ℝ)*X 1 2+(6742151871/10000000000 : ℝ)*X 2 0+(1095201237/2500000000 : ℝ)*X 2 1+(-287894579/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-2068529801/10000000000 : ℝ)*X 0 0+(3765048521/10000000000 : ℝ)*X 0 1+(-3338715143/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4072986833/10000000000 : ℝ)*X 1 0+(-82504173/500000000 : ℝ)*X 1 1+(-6699583509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4334849767/10000000000 : ℝ)*X 2 0+(1358679153/2000000000 : ℝ)*X 2 1+(283185927/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((126350053/200000000 : ℝ)*X 0 0+(5286514099/10000000000 : ℝ)*X 0 1+(-375184961/10000000000 : ℝ)*X 0 2+(126350053/200000000 : ℝ)*X 1 0+(5286514099/10000000000 : ℝ)*X 1 1+(-375184961/10000000000 : ℝ)*X 1 2+(126350053/200000000 : ℝ)*X 2 0+(5286514099/10000000000 : ℝ)*X 2 1+(-375184961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1365618163/10000000000 : ℝ)*X 0 0+(2147642859/5000000000 : ℝ)*X 0 1+(-668802163/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((403544463/1000000000 : ℝ)*X 1 0+(-366206583/2000000000 : ℝ)*X 1 1+(-6611217959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((566230741/1000000000 : ℝ)*X 2 0+(5492643279/10000000000 : ℝ)*X 2 1+(1221110441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3865266697/5000000000 : ℝ)*X 0 0+(3677573153/10000000000 : ℝ)*X 0 1+(-352577957/10000000000 : ℝ)*X 0 2+(3865266697/5000000000 : ℝ)*X 1 0+(3677573153/10000000000 : ℝ)*X 1 1+(-352577957/10000000000 : ℝ)*X 1 2+(3865266697/5000000000 : ℝ)*X 2 0+(3677573153/10000000000 : ℝ)*X 2 1+(-352577957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-110365139/1000000000 : ℝ)*X 0 0+(641755683/1250000000 : ℝ)*X 0 1+(-6082268831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((44237549/78125000 : ℝ)*X 1 0+(-415997859/2500000000 : ℝ)*X 1 1+(-5194516793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4191204169/10000000000 : ℝ)*X 2 0+(1578688697/2500000000 : ℝ)*X 2 1+(515432279/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((7956990381/10000000000 : ℝ)*X 0 0+(3356606831/10000000000 : ℝ)*X 0 1+(-103974641/2500000000 : ℝ)*X 0 2+(7956990381/10000000000 : ℝ)*X 1 0+(3356606831/10000000000 : ℝ)*X 1 1+(-103974641/2500000000 : ℝ)*X 1 2+(7956990381/10000000000 : ℝ)*X 2 0+(3356606831/10000000000 : ℝ)*X 2 1+(-103974641/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308060_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((22581/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22581/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (621143819046052091071152663/110122143250000000000000000000000 : ℝ) := by norm_num
    linear_combination (260287/100000000000 : ℝ)*(base5) + (1126603/200000000000 : ℝ)*(base39) + (585440974929/1000000000000 : ℝ)*(base59) + (2654843603021/500000000000 : ℝ)*(major_s3_0) + (2654843603021/500000000000 : ℝ)*(major_s3_1) + (2654843603021/500000000000 : ℝ)*(major_s3_2) + (8628917/500000000000 : ℝ)*(sp_s3_2) + (430049/1000000000000 : ℝ)*(sp_s3_6) + (3615584637467/500000000000 : ℝ)*(sp_s3_7) + (903852168379/125000000000 : ℝ)*(sp_s3_8) + (3615555685159/500000000000 : ℝ)*(sp_s3_9) + (3388200224059/1000000000000 : ℝ)*(sp_s3_13) + (175963951/500000000000 : ℝ)*(sp_s3_15) + (10812413/250000000000 : ℝ)*(sp_s3_23) + (3388203256977/1000000000000 : ℝ)*(f.failure) + (3615584637467/500000000000 : ℝ)*(f.sum) + (77268395001863323453/220244286500000000000000000000000 : ℝ)*base62 + (149742314068561/1499750000000000000000000000 : ℝ)*base64 + (164602961320853/458918750000000000000000000 : ℝ)*base66 + (147134796214191/2999500000000000000000000000 : ℝ)*base69 + (52842283876130573777/107977500750000000000000000000000 : ℝ)*base70 + (1094728076235499/3599850000000000000000000000 : ℝ)*base72 + (1198833695429/229459375000000000000000000 : ℝ)*base74 + (322701069765217/3599850000000000000000000000 : ℝ)*base77 + (927567182254353557/8260193310937500000000000000000 : ℝ)*base79 + (77353/100000000000000000 : ℝ)*base86 + (77353/100000000000000000 : ℝ)*base88 + (77353/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49211/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(49211/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36108378841764190814364525005787/5285642631713500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5070033/1000000000000 : ℝ)*(base18) + (36248052267/500000000000 : ℝ)*(base39) + (33106681803/125000000000 : ℝ)*(base59) + (5379329714313/1000000000000 : ℝ)*(major_s3_0) + (5379329714313/1000000000000 : ℝ)*(major_s3_1) + (5379329714313/1000000000000 : ℝ)*(major_s3_2) + (833329/250000000000 : ℝ)*(sp_s3_6) + (11824533/500000000000 : ℝ)*(sp_s3_7) + (75431579/1000000000000 : ℝ)*(sp_s3_8) + (3662995078093/500000000000 : ℝ)*(sp_s3_14) + (183148332591/25000000000 : ℝ)*(sp_s3_15) + (1831503451313/250000000000 : ℝ)*(sp_s3_16) + (3432499906457/1000000000000 : ℝ)*(sp_s3_20) + (140106459/1000000000000 : ℝ)*(sp_s3_27) + (3432643346231/1000000000000 : ℝ)*(f.failure) + (1831503451313/250000000000 : ℝ)*(f.sum) + (153539836484555340559/440488573000000000000000000000000 : ℝ)*base62 + (26785860614973/749875000000000000000000000 : ℝ)*base65 + (537897263929067/7342700000000000000000000000 : ℝ)*base66 + (2316526783795927/5999000000000000000000000000 : ℝ)*base68 + (110768755851568863/17996250125000000000000000000000 : ℝ)*base70 + (188146831643921/599975000000000000000000000 : ℝ)*base72 + (1595180939626807/7342700000000000000000000000 : ℝ)*base74 + (8385422532643/149993750000000000000000000 : ℝ)*base76 + (6031826990878328201/176217457300000000000000000000000 : ℝ)*base78 + (93759/100000000000000000 : ℝ)*base86 + (93759/100000000000000000 : ℝ)*base88 + (93759/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-33241/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-33241/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2750757372751812786348292221/2093323814540000000000000000000000 : ℝ) := by norm_num
    linear_combination (1478797/200000000000 : ℝ)*(base11) + (4804097/1000000000000 : ℝ)*(base15) + (525025164401/1000000000000 : ℝ)*(base39) + (38509/62500000000 : ℝ)*(base49) + (19899303749/100000000000 : ℝ)*(base59) + (169474260273/40000000000 : ℝ)*(major_s3_0) + (169474260273/40000000000 : ℝ)*(major_s3_1) + (169474260273/40000000000 : ℝ)*(major_s3_2) + (3485711/500000000000 : ℝ)*(sp_s3_9) + (12062199/1000000000000 : ℝ)*(sp_s3_20) + (360630859527/62500000000 : ℝ)*(sp_s3_21) + (72126204279/12500000000 : ℝ)*(sp_s3_22) + (1154018834999/200000000000 : ℝ)*(sp_s3_23) + (84487480219/31250000000 : ℝ)*(sp_s3_27) + (2703611429207/1000000000000 : ℝ)*(f.failure) + (5770101146417/1000000000000 : ℝ)*(f.sum) + (13820218921325153/174450920000000000000000000000 : ℝ)*base63 + (44735949024509/59990000000000000000000000 : ℝ)*base65 + (8509702687047/14540000000000000000000000 : ℝ)*base66 + (132755322623209/239960000000000000000000000 : ℝ)*base69 + (172726001892838229/1439700010000000000000000000000 : ℝ)*base71 + (718358506253/9599600000000000000000000 : ℝ)*base72 + (7457378138333/14540000000000000000000000 : ℝ)*base75 + (25320062064443/47998000000000000000000000 : ℝ)*base77 + (9943043095605459/348945460000000000000000000000 : ℝ)*base79 + (41823/100000000000000000 : ℝ)*base86 + (41823/100000000000000000 : ℝ)*base88 + (41823/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((71997/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71997/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(73427/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(73427/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5999/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5999/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22581/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22581/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49211/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(49211/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-33241/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-33241/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308060_s3 p hpa hpb X hX hprev2

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309060_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:04:03.791097+00:00
-- url     : https://prove2.me/submissions/3aa08c48-9acb-44a9-9587-61242a82b50b

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
theorem collision_support_c309060_s3_s3_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2431357943/10000000000 : ℝ)*x 0 + (792900821/2000000000 : ℝ)*x 1 + (-3102563553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2431357943/10000000000 : ℝ)^35 ≤ (7995547509309/50000000000000 : ℝ)^27 := by
    have hnat : (2431357943 : ℕ)^35*50000000000000^27 ≤ 7995547509309^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431357943 10000000000 7995547509309 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (792900821/2000000000 : ℝ)^35 ≤ (3767417370067/12500000000000 : ℝ)^27 := by
    have hnat : (792900821 : ℕ)^35*12500000000000^27 ≤ 3767417370067^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792900821 2000000000 3767417370067 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3102563553/5000000000 : ℝ)^35 ≤ (53869566004097/100000000000000 : ℝ)^27 := by
    have hnat : (3102563553 : ℕ)^35*100000000000000^27 ≤ 53869566004097^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102563553 5000000000 53869566004097 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2431357943/10000000000 : ℝ), (792900821/2000000000 : ℝ), (-3102563553/5000000000 : ℝ)] ![(7995547509309/50000000000000 : ℝ), (3767417370067/12500000000000 : ℝ), (53869566004097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2431357943/10000000000 : ℝ)|^35 ≤ (7995547509309/50000000000000 : ℝ)^27
        have hw : |(-2431357943/10000000000 : ℝ)|=(2431357943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(792900821/2000000000 : ℝ)|^35 ≤ (3767417370067/12500000000000 : ℝ)^27
        have hw : |(792900821/2000000000 : ℝ)|=(792900821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3102563553/5000000000 : ℝ)|^35 ≤ (53869566004097/100000000000000 : ℝ)^27
        have hw : |(-3102563553/5000000000 : ℝ)|=(3102563553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4484494509/10000000000 : ℝ)*x 0 + (-750949339/2500000000 : ℝ)*x 1 + (-1317887007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4484494509/10000000000 : ℝ)^35 ≤ (17680213288781/50000000000000 : ℝ)^27 := by
    have hnat : (4484494509 : ℕ)^35*50000000000000^27 ≤ 17680213288781^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484494509 10000000000 17680213288781 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750949339/2500000000 : ℝ)^35 ≤ (21033249479149/100000000000000 : ℝ)^27 := by
    have hnat : (750949339 : ℕ)^35*100000000000000^27 ≤ 21033249479149^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750949339 2500000000 21033249479149 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317887007/2500000000 : ℝ)^35 ≤ (2180316196229/5000000000000 : ℝ)^27 := by
    have hnat : (1317887007 : ℕ)^35*5000000000000^27 ≤ 2180316196229^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317887007 2500000000 2180316196229 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4484494509/10000000000 : ℝ), (-750949339/2500000000 : ℝ), (-1317887007/2500000000 : ℝ)] ![(17680213288781/50000000000000 : ℝ), (21033249479149/100000000000000 : ℝ), (2180316196229/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4484494509/10000000000 : ℝ)|^35 ≤ (17680213288781/50000000000000 : ℝ)^27
        have hw : |(4484494509/10000000000 : ℝ)|=(4484494509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-750949339/2500000000 : ℝ)|^35 ≤ (21033249479149/100000000000000 : ℝ)^27
        have hw : |(-750949339/2500000000 : ℝ)|=(750949339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1317887007/2500000000 : ℝ)|^35 ≤ (2180316196229/5000000000000 : ℝ)^27
        have hw : |(-1317887007/2500000000 : ℝ)|=(1317887007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4709792607/10000000000 : ℝ)*x 0 + (2797618291/5000000000 : ℝ)*x 1 + (2339388603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4709792607/10000000000 : ℝ)^35 ≤ (147188357151/390625000000 : ℝ)^27 := by
    have hnat : (4709792607 : ℕ)^35*390625000000^27 ≤ 147188357151^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4709792607 10000000000 147188357151 390625000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2797618291/5000000000 : ℝ)^35 ≤ (4710836121643/10000000000000 : ℝ)^27 := by
    have hnat : (2797618291 : ℕ)^35*10000000000000^27 ≤ 4710836121643^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797618291 5000000000 4710836121643 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2339388603/10000000000 : ℝ)^35 ≤ (1901427416287/12500000000000 : ℝ)^27 := by
    have hnat : (2339388603 : ℕ)^35*12500000000000^27 ≤ 1901427416287^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339388603 10000000000 1901427416287 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4709792607/10000000000 : ℝ), (2797618291/5000000000 : ℝ), (2339388603/10000000000 : ℝ)] ![(147188357151/390625000000 : ℝ), (4710836121643/10000000000000 : ℝ), (1901427416287/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4709792607/10000000000 : ℝ)|^35 ≤ (147188357151/390625000000 : ℝ)^27
        have hw : |(4709792607/10000000000 : ℝ)|=(4709792607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2797618291/5000000000 : ℝ)|^35 ≤ (4710836121643/10000000000000 : ℝ)^27
        have hw : |(2797618291/5000000000 : ℝ)|=(2797618291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2339388603/10000000000 : ℝ)|^35 ≤ (1901427416287/12500000000000 : ℝ)^27
        have hw : |(2339388603/10000000000 : ℝ)|=(2339388603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6420229049/10000000000 : ℝ)*x 0 + (873748733/2000000000 : ℝ)*x 1 + (-1629051267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6420229049/10000000000 : ℝ)^35 ≤ (11260520109221/20000000000000 : ℝ)^27 := by
    have hnat : (6420229049 : ℕ)^35*20000000000000^27 ≤ 11260520109221^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6420229049 10000000000 11260520109221 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873748733/2000000000 : ℝ)^35 ≤ (34181848506643/100000000000000 : ℝ)^27 := by
    have hnat : (873748733 : ℕ)^35*100000000000000^27 ≤ 34181848506643^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873748733 2000000000 34181848506643 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1629051267/10000000000 : ℝ)^35 ≤ (951555092281/10000000000000 : ℝ)^27 := by
    have hnat : (1629051267 : ℕ)^35*10000000000000^27 ≤ 951555092281^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629051267 10000000000 951555092281 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6420229049/10000000000 : ℝ), (873748733/2000000000 : ℝ), (-1629051267/10000000000 : ℝ)] ![(11260520109221/20000000000000 : ℝ), (34181848506643/100000000000000 : ℝ), (951555092281/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6420229049/10000000000 : ℝ)|^35 ≤ (11260520109221/20000000000000 : ℝ)^27
        have hw : |(6420229049/10000000000 : ℝ)|=(6420229049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873748733/2000000000 : ℝ)|^35 ≤ (34181848506643/100000000000000 : ℝ)^27
        have hw : |(873748733/2000000000 : ℝ)|=(873748733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1629051267/10000000000 : ℝ)|^35 ≤ (951555092281/10000000000000 : ℝ)^27
        have hw : |(-1629051267/10000000000 : ℝ)|=(1629051267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2394504899/10000000000 : ℝ)*x 0 + (1884048177/5000000000 : ℝ)*x 1 + (-80034671/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2394504899/10000000000 : ℝ)^35 ≤ (3919400634239/25000000000000 : ℝ)^27 := by
    have hnat : (2394504899 : ℕ)^35*25000000000000^27 ≤ 3919400634239^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394504899 10000000000 3919400634239 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884048177/5000000000 : ℝ)^35 ≤ (28218148718913/100000000000000 : ℝ)^27 := by
    have hnat : (1884048177 : ℕ)^35*100000000000000^27 ≤ 28218148718913^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884048177 5000000000 28218148718913 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80034671/125000000 : ℝ)^35 ≤ (56104248734241/100000000000000 : ℝ)^27 := by
    have hnat : (80034671 : ℕ)^35*100000000000000^27 ≤ 56104248734241^27*125000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80034671 125000000 56104248734241 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2394504899/10000000000 : ℝ), (1884048177/5000000000 : ℝ), (-80034671/125000000 : ℝ)] ![(3919400634239/25000000000000 : ℝ), (28218148718913/100000000000000 : ℝ), (56104248734241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2394504899/10000000000 : ℝ)|^35 ≤ (3919400634239/25000000000000 : ℝ)^27
        have hw : |(-2394504899/10000000000 : ℝ)|=(2394504899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1884048177/5000000000 : ℝ)|^35 ≤ (28218148718913/100000000000000 : ℝ)^27
        have hw : |(1884048177/5000000000 : ℝ)|=(1884048177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-80034671/125000000 : ℝ)|^35 ≤ (56104248734241/100000000000000 : ℝ)^27
        have hw : |(-80034671/125000000 : ℝ)|=(80034671/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (546649397/1250000000 : ℝ)*x 0 + (-1316691379/5000000000 : ℝ)*x 1 + (-5680286621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546649397/1250000000 : ℝ)^35 ≤ (855675114711/2500000000000 : ℝ)^27 := by
    have hnat : (546649397 : ℕ)^35*2500000000000^27 ≤ 855675114711^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546649397 1250000000 855675114711 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316691379/5000000000 : ℝ)^35 ≤ (1773431542049/10000000000000 : ℝ)^27 := by
    have hnat : (1316691379 : ℕ)^35*10000000000000^27 ≤ 1773431542049^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316691379 5000000000 1773431542049 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5680286621/10000000000 : ℝ)^35 ≤ (960773599493/2000000000000 : ℝ)^27 := by
    have hnat : (5680286621 : ℕ)^35*2000000000000^27 ≤ 960773599493^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680286621 10000000000 960773599493 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546649397/1250000000 : ℝ), (-1316691379/5000000000 : ℝ), (-5680286621/10000000000 : ℝ)] ![(855675114711/2500000000000 : ℝ), (1773431542049/10000000000000 : ℝ), (960773599493/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546649397/1250000000 : ℝ)|^35 ≤ (855675114711/2500000000000 : ℝ)^27
        have hw : |(546649397/1250000000 : ℝ)|=(546649397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1316691379/5000000000 : ℝ)|^35 ≤ (1773431542049/10000000000000 : ℝ)^27
        have hw : |(-1316691379/5000000000 : ℝ)|=(1316691379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5680286621/10000000000 : ℝ)|^35 ≤ (960773599493/2000000000000 : ℝ)^27
        have hw : |(-5680286621/10000000000 : ℝ)|=(5680286621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1149684739/2500000000 : ℝ)*x 0 + (749654007/1250000000 : ℝ)*x 1 + (969495307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1149684739/2500000000 : ℝ)^35 ≤ (36532540238407/100000000000000 : ℝ)^27 := by
    have hnat : (1149684739 : ℕ)^35*100000000000000^27 ≤ 36532540238407^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149684739 2500000000 36532540238407 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (749654007/1250000000 : ℝ)^35 ≤ (51541673327327/100000000000000 : ℝ)^27 := by
    have hnat : (749654007 : ℕ)^35*100000000000000^27 ≤ 51541673327327^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749654007 1250000000 51541673327327 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969495307/5000000000 : ℝ)^35 ≤ (5962893211199/50000000000000 : ℝ)^27 := by
    have hnat : (969495307 : ℕ)^35*50000000000000^27 ≤ 5962893211199^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969495307 5000000000 5962893211199 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1149684739/2500000000 : ℝ), (749654007/1250000000 : ℝ), (969495307/5000000000 : ℝ)] ![(36532540238407/100000000000000 : ℝ), (51541673327327/100000000000000 : ℝ), (5962893211199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1149684739/2500000000 : ℝ)|^35 ≤ (36532540238407/100000000000000 : ℝ)^27
        have hw : |(1149684739/2500000000 : ℝ)|=(1149684739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(749654007/1250000000 : ℝ)|^35 ≤ (51541673327327/100000000000000 : ℝ)^27
        have hw : |(749654007/1250000000 : ℝ)|=(749654007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(969495307/5000000000 : ℝ)|^35 ≤ (5962893211199/50000000000000 : ℝ)^27
        have hw : |(969495307/5000000000 : ℝ)|=(969495307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (158347337/250000000 : ℝ)*x 0 + (4758955687/10000000000 : ℝ)*x 1 + (-1212066373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158347337/250000000 : ℝ)^35 ≤ (5532310345977/10000000000000 : ℝ)^27 := by
    have hnat : (158347337 : ℕ)^35*10000000000000^27 ≤ 5532310345977^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158347337 250000000 5532310345977 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4758955687/10000000000 : ℝ)^35 ≤ (15276348301/40000000000 : ℝ)^27 := by
    have hnat : (4758955687 : ℕ)^35*40000000000^27 ≤ 15276348301^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4758955687 10000000000 15276348301 40000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1212066373/10000000000 : ℝ)^35 ≤ (6486025771381/100000000000000 : ℝ)^27 := by
    have hnat : (1212066373 : ℕ)^35*100000000000000^27 ≤ 6486025771381^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212066373 10000000000 6486025771381 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(158347337/250000000 : ℝ), (4758955687/10000000000 : ℝ), (-1212066373/10000000000 : ℝ)] ![(5532310345977/10000000000000 : ℝ), (15276348301/40000000000 : ℝ), (6486025771381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(158347337/250000000 : ℝ)|^35 ≤ (5532310345977/10000000000000 : ℝ)^27
        have hw : |(158347337/250000000 : ℝ)|=(158347337/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4758955687/10000000000 : ℝ)|^35 ≤ (15276348301/40000000000 : ℝ)^27
        have hw : |(4758955687/10000000000 : ℝ)|=(4758955687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1212066373/10000000000 : ℝ)|^35 ≤ (6486025771381/100000000000000 : ℝ)^27
        have hw : |(-1212066373/10000000000 : ℝ)|=(1212066373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084228527/10000000000 : ℝ)*x 0 + (401403381/1000000000 : ℝ)*x 1 + (-3208912397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084228527/10000000000 : ℝ)^35 ≤ (6548191407199/50000000000000 : ℝ)^27 := by
    have hnat : (2084228527 : ℕ)^35*50000000000000^27 ≤ 6548191407199^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084228527 10000000000 6548191407199 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401403381/1000000000 : ℝ)^35 ≤ (30628346559649/100000000000000 : ℝ)^27 := by
    have hnat : (401403381 : ℕ)^35*100000000000000^27 ≤ 30628346559649^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401403381 1000000000 30628346559649 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3208912397/5000000000 : ℝ)^35 ≤ (14068817652069/25000000000000 : ℝ)^27 := by
    have hnat : (3208912397 : ℕ)^35*25000000000000^27 ≤ 14068817652069^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3208912397 5000000000 14068817652069 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084228527/10000000000 : ℝ), (401403381/1000000000 : ℝ), (-3208912397/5000000000 : ℝ)] ![(6548191407199/50000000000000 : ℝ), (30628346559649/100000000000000 : ℝ), (14068817652069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084228527/10000000000 : ℝ)|^35 ≤ (6548191407199/50000000000000 : ℝ)^27
        have hw : |(-2084228527/10000000000 : ℝ)|=(2084228527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401403381/1000000000 : ℝ)|^35 ≤ (30628346559649/100000000000000 : ℝ)^27
        have hw : |(401403381/1000000000 : ℝ)|=(401403381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3208912397/5000000000 : ℝ)|^35 ≤ (14068817652069/25000000000000 : ℝ)^27
        have hw : |(-3208912397/5000000000 : ℝ)|=(3208912397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (855371407/2000000000 : ℝ)*x 0 + (-1396305111/5000000000 : ℝ)*x 1 + (-5641195821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855371407/2000000000 : ℝ)^35 ≤ (33252810523057/100000000000000 : ℝ)^27 := by
    have hnat : (855371407 : ℕ)^35*100000000000000^27 ≤ 33252810523057^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855371407 2000000000 33252810523057 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1396305111/5000000000 : ℝ)^35 ≤ (765464801619/4000000000000 : ℝ)^27 := by
    have hnat : (1396305111 : ℕ)^35*4000000000000^27 ≤ 765464801619^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396305111 5000000000 765464801619 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5641195821/10000000000 : ℝ)^35 ≤ (4761056942177/10000000000000 : ℝ)^27 := by
    have hnat : (5641195821 : ℕ)^35*10000000000000^27 ≤ 4761056942177^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5641195821 10000000000 4761056942177 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855371407/2000000000 : ℝ), (-1396305111/5000000000 : ℝ), (-5641195821/10000000000 : ℝ)] ![(33252810523057/100000000000000 : ℝ), (765464801619/4000000000000 : ℝ), (4761056942177/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855371407/2000000000 : ℝ)|^35 ≤ (33252810523057/100000000000000 : ℝ)^27
        have hw : |(855371407/2000000000 : ℝ)|=(855371407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1396305111/5000000000 : ℝ)|^35 ≤ (765464801619/4000000000000 : ℝ)^27
        have hw : |(-1396305111/5000000000 : ℝ)|=(1396305111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5641195821/10000000000 : ℝ)|^35 ≤ (4761056942177/10000000000000 : ℝ)^27
        have hw : |(-5641195821/10000000000 : ℝ)|=(5641195821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2532373443/5000000000 : ℝ)*x 0 + (1381631429/2500000000 : ℝ)*x 1 + (247260081/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2532373443/5000000000 : ℝ)^35 ≤ (20700903689759/50000000000000 : ℝ)^27 := by
    have hnat : (2532373443 : ℕ)^35*50000000000000^27 ≤ 20700903689759^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532373443 5000000000 20700903689759 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1381631429/2500000000 : ℝ)^35 ≤ (11589954825813/25000000000000 : ℝ)^27 := by
    have hnat : (1381631429 : ℕ)^35*25000000000000^27 ≤ 11589954825813^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381631429 2500000000 11589954825813 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247260081/1250000000 : ℝ)^35 ≤ (1223837330147/10000000000000 : ℝ)^27 := by
    have hnat : (247260081 : ℕ)^35*10000000000000^27 ≤ 1223837330147^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247260081 1250000000 1223837330147 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2532373443/5000000000 : ℝ), (1381631429/2500000000 : ℝ), (247260081/1250000000 : ℝ)] ![(20700903689759/50000000000000 : ℝ), (11589954825813/25000000000000 : ℝ), (1223837330147/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2532373443/5000000000 : ℝ)|^35 ≤ (20700903689759/50000000000000 : ℝ)^27
        have hw : |(2532373443/5000000000 : ℝ)|=(2532373443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1381631429/2500000000 : ℝ)|^35 ≤ (11589954825813/25000000000000 : ℝ)^27
        have hw : |(1381631429/2500000000 : ℝ)|=(1381631429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(247260081/1250000000 : ℝ)|^35 ≤ (1223837330147/10000000000000 : ℝ)^27
        have hw : |(247260081/1250000000 : ℝ)|=(247260081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6884640079/10000000000 : ℝ)*x 0 + (4162372801/10000000000 : ℝ)*x 1 + (-1179176329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6884640079/10000000000 : ℝ)^35 ≤ (61637647221949/100000000000000 : ℝ)^27 := by
    have hnat : (6884640079 : ℕ)^35*100000000000000^27 ≤ 61637647221949^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6884640079 10000000000 61637647221949 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4162372801/10000000000 : ℝ)^35 ≤ (3210355417971/10000000000000 : ℝ)^27 := by
    have hnat : (4162372801 : ℕ)^35*10000000000000^27 ≤ 3210355417971^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162372801 10000000000 3210355417971 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1179176329/10000000000 : ℝ)^35 ≤ (625879858143/10000000000000 : ℝ)^27 := by
    have hnat : (1179176329 : ℕ)^35*10000000000000^27 ≤ 625879858143^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179176329 10000000000 625879858143 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6884640079/10000000000 : ℝ), (4162372801/10000000000 : ℝ), (-1179176329/10000000000 : ℝ)] ![(61637647221949/100000000000000 : ℝ), (3210355417971/10000000000000 : ℝ), (625879858143/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6884640079/10000000000 : ℝ)|^35 ≤ (61637647221949/100000000000000 : ℝ)^27
        have hw : |(6884640079/10000000000 : ℝ)|=(6884640079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4162372801/10000000000 : ℝ)|^35 ≤ (3210355417971/10000000000000 : ℝ)^27
        have hw : |(4162372801/10000000000 : ℝ)|=(4162372801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1179176329/10000000000 : ℝ)|^35 ≤ (625879858143/10000000000000 : ℝ)^27
        have hw : |(-1179176329/10000000000 : ℝ)|=(1179176329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-396972869/2000000000 : ℝ)*x 0 + (4283585191/10000000000 : ℝ)*x 1 + (-3125508087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396972869/2000000000 : ℝ)^35 ≤ (12292807375553/100000000000000 : ℝ)^27 := by
    have hnat : (396972869 : ℕ)^35*100000000000000^27 ≤ 12292807375553^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396972869 2000000000 12292807375553 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4283585191/10000000000 : ℝ)^35 ≤ (8330159479011/25000000000000 : ℝ)^27 := by
    have hnat : (4283585191 : ℕ)^35*25000000000000^27 ≤ 8330159479011^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283585191 10000000000 8330159479011 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3125508087/5000000000 : ℝ)^35 ≤ (3399159668649/6250000000000 : ℝ)^27 := by
    have hnat : (3125508087 : ℕ)^35*6250000000000^27 ≤ 3399159668649^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3125508087 5000000000 3399159668649 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396972869/2000000000 : ℝ), (4283585191/10000000000 : ℝ), (-3125508087/5000000000 : ℝ)] ![(12292807375553/100000000000000 : ℝ), (8330159479011/25000000000000 : ℝ), (3399159668649/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396972869/2000000000 : ℝ)|^35 ≤ (12292807375553/100000000000000 : ℝ)^27
        have hw : |(-396972869/2000000000 : ℝ)|=(396972869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4283585191/10000000000 : ℝ)|^35 ≤ (8330159479011/25000000000000 : ℝ)^27
        have hw : |(4283585191/10000000000 : ℝ)|=(4283585191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3125508087/5000000000 : ℝ)|^35 ≤ (3399159668649/6250000000000 : ℝ)^27
        have hw : |(-3125508087/5000000000 : ℝ)|=(3125508087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4938566393/10000000000 : ℝ)*x 0 + (-2692351923/10000000000 : ℝ)*x 1 + (-2545466671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4938566393/10000000000 : ℝ)^35 ≤ (20034844755073/50000000000000 : ℝ)^27 := by
    have hnat : (4938566393 : ℕ)^35*50000000000000^27 ≤ 20034844755073^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4938566393 10000000000 20034844755073 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692351923/10000000000 : ℝ)^35 ≤ (9125401928389/50000000000000 : ℝ)^27 := by
    have hnat : (2692351923 : ℕ)^35*50000000000000^27 ≤ 9125401928389^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692351923 10000000000 9125401928389 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2545466671/5000000000 : ℝ)^35 ≤ (20839753309511/50000000000000 : ℝ)^27 := by
    have hnat : (2545466671 : ℕ)^35*50000000000000^27 ≤ 20839753309511^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545466671 5000000000 20839753309511 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4938566393/10000000000 : ℝ), (-2692351923/10000000000 : ℝ), (-2545466671/5000000000 : ℝ)] ![(20034844755073/50000000000000 : ℝ), (9125401928389/50000000000000 : ℝ), (20839753309511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4938566393/10000000000 : ℝ)|^35 ≤ (20034844755073/50000000000000 : ℝ)^27
        have hw : |(4938566393/10000000000 : ℝ)|=(4938566393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2692351923/10000000000 : ℝ)|^35 ≤ (9125401928389/50000000000000 : ℝ)^27
        have hw : |(-2692351923/10000000000 : ℝ)|=(2692351923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2545466671/5000000000 : ℝ)|^35 ≤ (20839753309511/50000000000000 : ℝ)^27
        have hw : |(-2545466671/5000000000 : ℝ)|=(2545466671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4456458777/10000000000 : ℝ)*x 0 + (722639/1250000 : ℝ)*x 1 + (12032191/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4456458777/10000000000 : ℝ)^35 ≤ (4384266166769/12500000000000 : ℝ)^27 := by
    have hnat : (4456458777 : ℕ)^35*12500000000000^27 ≤ 4384266166769^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4456458777 10000000000 4384266166769 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (722639/1250000 : ℝ)^35 ≤ (6143364029709/12500000000000 : ℝ)^27 := by
    have hnat : (722639 : ℕ)^35*12500000000000^27 ≤ 6143364029709^27*1250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722639 1250000 6143364029709 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12032191/50000000 : ℝ)^35 ≤ (15778958417031/100000000000000 : ℝ)^27 := by
    have hnat : (12032191 : ℕ)^35*100000000000000^27 ≤ 15778958417031^27*50000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12032191 50000000 15778958417031 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4456458777/10000000000 : ℝ), (722639/1250000 : ℝ), (12032191/50000000 : ℝ)] ![(4384266166769/12500000000000 : ℝ), (6143364029709/12500000000000 : ℝ), (15778958417031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4456458777/10000000000 : ℝ)|^35 ≤ (4384266166769/12500000000000 : ℝ)^27
        have hw : |(4456458777/10000000000 : ℝ)|=(4456458777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(722639/1250000 : ℝ)|^35 ≤ (6143364029709/12500000000000 : ℝ)^27
        have hw : |(722639/1250000 : ℝ)|=(722639/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12032191/50000000 : ℝ)|^35 ≤ (15778958417031/100000000000000 : ℝ)^27
        have hw : |(12032191/50000000 : ℝ)|=(12032191/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309060_s3_s3_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1397004899/2000000000 : ℝ)*x 0 + (497001629/1250000000 : ℝ)*x 1 + (-638643893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1397004899/2000000000 : ℝ)^35 ≤ (31402590334347/50000000000000 : ℝ)^27 := by
    have hnat : (1397004899 : ℕ)^35*50000000000000^27 ≤ 31402590334347^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397004899 2000000000 31402590334347 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497001629/1250000000 : ℝ)^35 ≤ (30252806223157/100000000000000 : ℝ)^27 := by
    have hnat : (497001629 : ℕ)^35*100000000000000^27 ≤ 30252806223157^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497001629 1250000000 30252806223157 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638643893/5000000000 : ℝ)^35 ≤ (6942013097051/100000000000000 : ℝ)^27 := by
    have hnat : (638643893 : ℕ)^35*100000000000000^27 ≤ 6942013097051^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638643893 5000000000 6942013097051 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1397004899/2000000000 : ℝ), (497001629/1250000000 : ℝ), (-638643893/5000000000 : ℝ)] ![(31402590334347/50000000000000 : ℝ), (30252806223157/100000000000000 : ℝ), (6942013097051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1397004899/2000000000 : ℝ)|^35 ≤ (31402590334347/50000000000000 : ℝ)^27
        have hw : |(1397004899/2000000000 : ℝ)|=(1397004899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(497001629/1250000000 : ℝ)|^35 ≤ (30252806223157/100000000000000 : ℝ)^27
        have hw : |(497001629/1250000000 : ℝ)|=(497001629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-638643893/5000000000 : ℝ)|^35 ≤ (6942013097051/100000000000000 : ℝ)^27
        have hw : |(-638643893/5000000000 : ℝ)|=(638643893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309060_s3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((60861/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60861/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15993/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15993/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23649/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23649/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2711/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2711/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15053/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15053/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17227/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17227/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s3_pow0 : (60861/100000 : ℝ) ^ (69/16 : ℝ) ≤ (2936988919797967367/25000000000000000000 : ℝ) := by
    have hpowers : (60861/100000 : ℝ)^69 ≤ (2936988919797967367/25000000000000000000 : ℝ)^16 := by
      have hnat : (60861 : ℕ)^69*25000000000000000000^16 ≤ 2936988919797967367^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60861 100000 2936988919797967367 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60861/100000 : ℝ)) (X := (2936988919797967367/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (27936988919797967367/25000000000000000000 : ℝ) ≤ (1282614083125049/1250000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (27936988919797967367/25000000000000000000 : ℝ)^16 ≤ (1282614083125049/1250000000000000 : ℝ)^69 := by
      have hnat : (27936988919797967367 : ℕ)^16*1250000000000000^69 ≤ 1282614083125049^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27936988919797967367 25000000000000000000 1282614083125049 1250000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1282614083125049/1250000000000000 : ℝ)) (X := (27936988919797967367/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (15436988919797967367/12500000000000000000 : ℝ) ≤ (1050153470727433/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (15436988919797967367/12500000000000000000 : ℝ)^16 ≤ (1050153470727433/1000000000000000 : ℝ)^69 := by
      have hnat : (15436988919797967367 : ℕ)^16*1000000000000000^69 ≤ 1050153470727433^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15436988919797967367 12500000000000000000 1050153470727433 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1050153470727433/1000000000000000 : ℝ)) (X := (15436988919797967367/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(10871361041683/253587500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(40103673712323/1014350000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (60861/100000 : ℝ)) (alpha := (10871361041683/253587500000000 : ℝ)) (beta := (40103673712323/1014350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (60861/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(10871361041683/253587500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(40103673712323/1014350000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (15993/25000 : ℝ) ^ (69/16 : ℝ) ≤ (7282853456714860159/50000000000000000000 : ℝ) := by
    have hpowers : (15993/25000 : ℝ)^69 ≤ (7282853456714860159/50000000000000000000 : ℝ)^16 := by
      have hnat : (15993 : ℕ)^69*50000000000000000000^16 ≤ 7282853456714860159^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15993 25000 7282853456714860159 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15993/25000 : ℝ)) (X := (7282853456714860159/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (57282853456714860159/50000000000000000000 : ℝ) ≤ (5160167910895839/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (57282853456714860159/50000000000000000000 : ℝ)^16 ≤ (5160167910895839/5000000000000000 : ℝ)^69 := by
      have hnat : (57282853456714860159 : ℕ)^16*5000000000000000^69 ≤ 5160167910895839^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57282853456714860159 50000000000000000000 5160167910895839 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5160167910895839/5000000000000000 : ℝ)) (X := (57282853456714860159/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (32282853456714860159/25000000000000000000 : ℝ) ≤ (5305380456888689/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (32282853456714860159/25000000000000000000 : ℝ)^16 ≤ (5305380456888689/5000000000000000 : ℝ)^69 := by
      have hnat : (32282853456714860159 : ℕ)^16*5000000000000000^69 ≤ 5305380456888689^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32282853456714860159 25000000000000000000 5305380456888689 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5305380456888689/5000000000000000 : ℝ)) (X := (32282853456714860159/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(160167910895839/3198600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(2904250919857/63972000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (15993/25000 : ℝ)) (alpha := (160167910895839/3198600000000000 : ℝ)) (beta := (2904250919857/63972000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (15993/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(160167910895839/3198600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(2904250919857/63972000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (23649/50000 : ℝ) ^ (69/16 : ℝ) ≤ (792117250342522343/20000000000000000000 : ℝ) := by
    have hpowers : (23649/50000 : ℝ)^69 ≤ (792117250342522343/20000000000000000000 : ℝ)^16 := by
      have hnat : (23649 : ℕ)^69*20000000000000000000^16 ≤ 792117250342522343^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23649 50000 792117250342522343 20000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23649/50000 : ℝ)) (X := (792117250342522343/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (20792117250342522343/20000000000000000000 : ℝ) ≤ (2522618613405589/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (20792117250342522343/20000000000000000000 : ℝ)^16 ≤ (2522618613405589/2500000000000000 : ℝ)^69 := by
      have hnat : (20792117250342522343 : ℕ)^16*2500000000000000^69 ≤ 2522618613405589^69*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20792117250342522343 20000000000000000000 2522618613405589 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2522618613405589/2500000000000000 : ℝ)) (X := (20792117250342522343/20000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (10792117250342522343/10000000000000000000 : ℝ) ≤ (2544584715548481/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (10792117250342522343/10000000000000000000 : ℝ)^16 ≤ (2544584715548481/2500000000000000 : ℝ)^69 := by
      have hnat : (10792117250342522343 : ℕ)^16*2500000000000000^69 ≤ 2544584715548481^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10792117250342522343 10000000000000000000 2544584715548481 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2544584715548481/2500000000000000 : ℝ)) (X := (10792117250342522343/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(7539537801863/394150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5491525535723/295612500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (23649/50000 : ℝ)) (alpha := (7539537801863/394150000000000 : ℝ)) (beta := (5491525535723/295612500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (23649/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(7539537801863/394150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5491525535723/295612500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2431357943/10000000000 : ℝ)*X 0 0+(792900821/2000000000 : ℝ)*X 0 1+(-3102563553/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((4484494509/10000000000 : ℝ)*X 1 0+(-750949339/2500000000 : ℝ)*X 1 1+(-1317887007/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((4709792607/10000000000 : ℝ)*X 2 0+(2797618291/5000000000 : ℝ)*X 2 1+(2339388603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((6420229049/10000000000 : ℝ)*X 0 0+(873748733/2000000000 : ℝ)*X 0 1+(-1629051267/10000000000 : ℝ)*X 0 2+(6420229049/10000000000 : ℝ)*X 1 0+(873748733/2000000000 : ℝ)*X 1 1+(-1629051267/10000000000 : ℝ)*X 1 2+(6420229049/10000000000 : ℝ)*X 2 0+(873748733/2000000000 : ℝ)*X 2 1+(-1629051267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-2394504899/10000000000 : ℝ)*X 0 0+(1884048177/5000000000 : ℝ)*X 0 1+(-80034671/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((546649397/1250000000 : ℝ)*X 1 0+(-1316691379/5000000000 : ℝ)*X 1 1+(-5680286621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((1149684739/2500000000 : ℝ)*X 2 0+(749654007/1250000000 : ℝ)*X 2 1+(969495307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((158347337/250000000 : ℝ)*X 0 0+(4758955687/10000000000 : ℝ)*X 0 1+(-1212066373/10000000000 : ℝ)*X 0 2+(158347337/250000000 : ℝ)*X 1 0+(4758955687/10000000000 : ℝ)*X 1 1+(-1212066373/10000000000 : ℝ)*X 1 2+(158347337/250000000 : ℝ)*X 2 0+(4758955687/10000000000 : ℝ)*X 2 1+(-1212066373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-2084228527/10000000000 : ℝ)*X 0 0+(401403381/1000000000 : ℝ)*X 0 1+(-3208912397/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((855371407/2000000000 : ℝ)*X 1 0+(-1396305111/5000000000 : ℝ)*X 1 1+(-5641195821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((2532373443/5000000000 : ℝ)*X 2 0+(1381631429/2500000000 : ℝ)*X 2 1+(247260081/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((6884640079/10000000000 : ℝ)*X 0 0+(4162372801/10000000000 : ℝ)*X 0 1+(-1179176329/10000000000 : ℝ)*X 0 2+(6884640079/10000000000 : ℝ)*X 1 0+(4162372801/10000000000 : ℝ)*X 1 1+(-1179176329/10000000000 : ℝ)*X 1 2+(6884640079/10000000000 : ℝ)*X 2 0+(4162372801/10000000000 : ℝ)*X 2 1+(-1179176329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-396972869/2000000000 : ℝ)*X 0 0+(4283585191/10000000000 : ℝ)*X 0 1+(-3125508087/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((4938566393/10000000000 : ℝ)*X 1 0+(-2692351923/10000000000 : ℝ)*X 1 1+(-2545466671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4456458777/10000000000 : ℝ)*X 2 0+(722639/1250000 : ℝ)*X 2 1+(12032191/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((1397004899/2000000000 : ℝ)*X 0 0+(497001629/1250000000 : ℝ)*X 0 1+(-638643893/5000000000 : ℝ)*X 0 2+(1397004899/2000000000 : ℝ)*X 1 0+(497001629/1250000000 : ℝ)*X 1 1+(-638643893/5000000000 : ℝ)*X 1 2+(1397004899/2000000000 : ℝ)*X 2 0+(497001629/1250000000 : ℝ)*X 2 1+(-638643893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309060_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((2711/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2711/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (253683877449895409510912987873/14209107105850000000000000000000000 : ℝ) := by norm_num
    linear_combination (5685141/500000000000 : ℝ)*(base5) + (133209338589/100000000000 : ℝ)*(base39) + (1451551/1000000000000 : ℝ)*(base49) + (2100847802423/1000000000000 : ℝ)*(base59) + (6343789829811/500000000000 : ℝ)*(major_s3_0) + (6343789829811/500000000000 : ℝ)*(major_s3_1) + (6343789829811/500000000000 : ℝ)*(major_s3_2) + (124468441/500000000000 : ℝ)*(sp_s3_1) + (17407920290101/1000000000000 : ℝ)*(sp_s3_7) + (8703620931951/500000000000 : ℝ)*(sp_s3_8) + (3481524920009/200000000000 : ℝ)*(sp_s3_9) + (1593444341531/200000000000 : ℝ)*(sp_s3_13) + (429489317/1000000000000 : ℝ)*(sp_s3_15) + (153530169/500000000000 : ℝ)*(sp_s3_23) + (7967233077937/1000000000000 : ℝ)*(f.failure) + (17407920290101/1000000000000 : ℝ)*(f.sum) + (1357711453279427129/4202427300000000000000000000000 : ℝ)*base62 + (79515517488293/394150000000000000000000000 : ℝ)*base64 + (2855092749461/5331000000000000000000000 : ℝ)*base66 + (15222392145989/394150000000000000000000000 : ℝ)*base68 + (3859414497491123879/7996121050000000000000000000000 : ℝ)*base70 + (9491323241843/126793750000000000000000000 : ℝ)*base72 + (19686439909883/533100000000000000000000000 : ℝ)*base75 + (144233019700629/1014350000000000000000000000 : ℝ)*base77 + (27683772550560407/2703749925000000000000000000000 : ℝ)*base78 + (33439/100000000000000000 : ℝ)*base87 + (33439/100000000000000000 : ℝ)*base89 + (33439/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15053/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15053/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (729919773000580559702246475583/42627321317550000000000000000000000 : ℝ) := by norm_num
    linear_combination (1457041646943/1000000000000 : ℝ)*(base39) + (946616985681/500000000000 : ℝ)*(base59) + (1620097283309/125000000000 : ℝ)*(major_s3_0) + (1620097283309/125000000000 : ℝ)*(major_s3_1) + (1620097283309/125000000000 : ℝ)*(major_s3_2) + (34143551/1000000000000 : ℝ)*(sp_s3_0) + (121828361/1000000000000 : ℝ)*(sp_s3_2) + (12423497/1000000000000 : ℝ)*(sp_s3_6) + (244228989/1000000000000 : ℝ)*(sp_s3_7) + (17782482857561/1000000000000 : ℝ)*(sp_s3_14) + (17782761230101/1000000000000 : ℝ)*(sp_s3_15) + (17782639401739/1000000000000 : ℝ)*(sp_s3_16) + (8138384749131/1000000000000 : ℝ)*(sp_s3_20) + (392422449/1000000000000 : ℝ)*(sp_s3_27) + (8138789595077/1000000000000 : ℝ)*(f.failure) + (17782761230101/1000000000000 : ℝ)*(f.sum) + (27615027121739207/787955118750000000000000000000 : ℝ)*base62 + (583158346119899/1182450000000000000000000000 : ℝ)*base64 + (11083781888689/39982500000000000000000000 : ℝ)*base67 + (31800573303711/98537500000000000000000000 : ℝ)*base68 + (2244063003458026561/11994181575000000000000000000000 : ℝ)*base70 + (739957527702811/1014350000000000000000000000 : ℝ)*base73 + (3482250241151/24989062500000000000000000 : ℝ)*base75 + (129443621383227/507175000000000000000000000 : ℝ)*base77 + (9955761435176690843/16222499550000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (27019/100000000000000000 : ℝ)*base87 + (27019/100000000000000000 : ℝ)*base89 + (27019/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17227/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17227/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (75424119599133597581140889087/17050928527020000000000000000000000 : ℝ) := by norm_num
    linear_combination (849862539709/500000000000 : ℝ)*(base39) + (103069/62500000000 : ℝ)*(base40) + (1483323745661/1000000000000 : ℝ)*(base59) + (10299420435793/1000000000000 : ℝ)*(major_s3_0) + (10299420435793/1000000000000 : ℝ)*(major_s3_1) + (10299420435793/1000000000000 : ℝ)*(major_s3_2) + (3903447/200000000000 : ℝ)*(sp_s3_0) + (4367977/50000000000 : ℝ)*(sp_s3_2) + (790927/31250000000 : ℝ)*(sp_s3_9) + (194799957/1000000000000 : ℝ)*(sp_s3_20) + (14131244078877/1000000000000 : ℝ)*(sp_s3_21) + (14131263596111/1000000000000 : ℝ)*(sp_s3_22) + (14131150926907/1000000000000 : ℝ)*(sp_s3_23) + (6467381001027/1000000000000 : ℝ)*(sp_s3_27) + (808446975123/125000000000 : ℝ)*(f.failure) + (14131263596111/1000000000000 : ℝ)*(f.sum) + (5239366609718031449/25214563800000000000000000000000 : ℝ)*base63 + (62649960820091/1182450000000000000000000000 : ℝ)*base64 + (167552536427843/319860000000000000000000000 : ℝ)*base67 + (20182179019047/197075000000000000000000000 : ℝ)*base69 + (1338193558607744729/2998545393750000000000000000000 : ℝ)*base71 + (335325745412383/507175000000000000000000000 : ℝ)*base72 + (282341564863267/3198600000000000000000000000 : ℝ)*base75 + (280446509038501/1014350000000000000000000000 : ℝ)*base77 + (17821482034522277081/32444999100000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (119/12500000000000000 : ℝ)*base86 + (119/12500000000000000 : ℝ)*base88 + (119/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((60861/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60861/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15993/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15993/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23649/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23649/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2711/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2711/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15053/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15053/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17227/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17227/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309060_s3 p hpa hpb X hX hprev2

#print axioms solution

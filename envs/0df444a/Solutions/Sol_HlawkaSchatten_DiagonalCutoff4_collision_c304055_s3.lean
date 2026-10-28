-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304055_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:27.998876+00:00
-- url     : https://prove2.me/submissions/427bccbc-6d61-43a5-a4b4-4596837b6640

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
theorem collision_support_c304055_s3_s3_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-29295161/250000000 : ℝ)*x 0 + (6034986699/10000000000 : ℝ)*x 1 + (5233921391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29295161/250000000 : ℝ)^133 ≤ (5940731466563/100000000000000 : ℝ)^101 := by
    have hnat : (29295161 : ℕ)^133*100000000000000^101 ≤ 5940731466563^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29295161 250000000 5940731466563 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6034986699/10000000000 : ℝ)^133 ≤ (12856644470551/25000000000000 : ℝ)^101 := by
    have hnat : (6034986699 : ℕ)^133*25000000000000^101 ≤ 12856644470551^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6034986699 10000000000 12856644470551 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233921391/10000000000 : ℝ)^133 ≤ (42632690638861/100000000000000 : ℝ)^101 := by
    have hnat : (5233921391 : ℕ)^133*100000000000000^101 ≤ 42632690638861^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233921391 10000000000 42632690638861 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29295161/250000000 : ℝ), (6034986699/10000000000 : ℝ), (5233921391/10000000000 : ℝ)] ![(5940731466563/100000000000000 : ℝ), (12856644470551/25000000000000 : ℝ), (42632690638861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29295161/250000000 : ℝ)|^133 ≤ (5940731466563/100000000000000 : ℝ)^101
        have hw : |(-29295161/250000000 : ℝ)|=(29295161/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6034986699/10000000000 : ℝ)|^133 ≤ (12856644470551/25000000000000 : ℝ)^101
        have hw : |(6034986699/10000000000 : ℝ)|=(6034986699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233921391/10000000000 : ℝ)|^133 ≤ (42632690638861/100000000000000 : ℝ)^101
        have hw : |(5233921391/10000000000 : ℝ)|=(5233921391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (826877473/1250000000 : ℝ)*x 0 + (476763571/1250000000 : ℝ)*x 1 + (1115113723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826877473/1250000000 : ℝ)^133 ≤ (29016146352863/50000000000000 : ℝ)^101 := by
    have hnat : (826877473 : ℕ)^133*50000000000000^101 ≤ 29016146352863^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826877473 1250000000 29016146352863 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476763571/1250000000 : ℝ)^133 ≤ (28103803923229/100000000000000 : ℝ)^101 := by
    have hnat : (476763571 : ℕ)^133*100000000000000^101 ≤ 28103803923229^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476763571 1250000000 28103803923229 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115113723/5000000000 : ℝ)^133 ≤ (6931951679593/50000000000000 : ℝ)^101 := by
    have hnat : (1115113723 : ℕ)^133*50000000000000^101 ≤ 6931951679593^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115113723 5000000000 6931951679593 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(826877473/1250000000 : ℝ), (476763571/1250000000 : ℝ), (1115113723/5000000000 : ℝ)] ![(29016146352863/50000000000000 : ℝ), (28103803923229/100000000000000 : ℝ), (6931951679593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(826877473/1250000000 : ℝ)|^133 ≤ (29016146352863/50000000000000 : ℝ)^101
        have hw : |(826877473/1250000000 : ℝ)|=(826877473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(476763571/1250000000 : ℝ)|^133 ≤ (28103803923229/100000000000000 : ℝ)^101
        have hw : |(476763571/1250000000 : ℝ)|=(476763571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1115113723/5000000000 : ℝ)|^133 ≤ (6931951679593/50000000000000 : ℝ)^101
        have hw : |(1115113723/5000000000 : ℝ)|=(1115113723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2881770091/10000000000 : ℝ)*x 0 + (1060849003/2500000000 : ℝ)*x 1 + (5747830057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2881770091/10000000000 : ℝ)^133 ≤ (19429529571057/100000000000000 : ℝ)^101 := by
    have hnat : (2881770091 : ℕ)^133*100000000000000^101 ≤ 19429529571057^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2881770091 10000000000 19429529571057 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060849003/2500000000 : ℝ)^133 ≤ (1010674823711/3125000000000 : ℝ)^101 := by
    have hnat : (1060849003 : ℕ)^133*3125000000000^101 ≤ 1010674823711^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060849003 2500000000 1010674823711 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5747830057/10000000000 : ℝ)^133 ≤ (4822887604681/10000000000000 : ℝ)^101 := by
    have hnat : (5747830057 : ℕ)^133*10000000000000^101 ≤ 4822887604681^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5747830057 10000000000 4822887604681 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2881770091/10000000000 : ℝ), (1060849003/2500000000 : ℝ), (5747830057/10000000000 : ℝ)] ![(19429529571057/100000000000000 : ℝ), (1010674823711/3125000000000 : ℝ), (4822887604681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2881770091/10000000000 : ℝ)|^133 ≤ (19429529571057/100000000000000 : ℝ)^101
        have hw : |(-2881770091/10000000000 : ℝ)|=(2881770091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060849003/2500000000 : ℝ)|^133 ≤ (1010674823711/3125000000000 : ℝ)^101
        have hw : |(1060849003/2500000000 : ℝ)|=(1060849003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5747830057/10000000000 : ℝ)|^133 ≤ (4822887604681/10000000000000 : ℝ)^101
        have hw : |(5747830057/10000000000 : ℝ)|=(5747830057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (665066289/2500000000 : ℝ)*x 0 + (3137783/5000000000 : ℝ)*x 1 + (8641352851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (665066289/2500000000 : ℝ)^133 ≤ (17487306521491/100000000000000 : ℝ)^101 := by
    have hnat : (665066289 : ℕ)^133*100000000000000^101 ≤ 17487306521491^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665066289 2500000000 17487306521491 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3137783/5000000000 : ℝ)^133 ≤ (6068032247/100000000000000 : ℝ)^101 := by
    have hnat : (3137783 : ℕ)^133*100000000000000^101 ≤ 6068032247^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137783 5000000000 6068032247 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8641352851/10000000000 : ℝ)^133 ≤ (10313328179117/12500000000000 : ℝ)^101 := by
    have hnat : (8641352851 : ℕ)^133*12500000000000^101 ≤ 10313328179117^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8641352851 10000000000 10313328179117 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(665066289/2500000000 : ℝ), (3137783/5000000000 : ℝ), (8641352851/10000000000 : ℝ)] ![(17487306521491/100000000000000 : ℝ), (6068032247/100000000000000 : ℝ), (10313328179117/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(665066289/2500000000 : ℝ)|^133 ≤ (17487306521491/100000000000000 : ℝ)^101
        have hw : |(665066289/2500000000 : ℝ)|=(665066289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3137783/5000000000 : ℝ)|^133 ≤ (6068032247/100000000000000 : ℝ)^101
        have hw : |(3137783/5000000000 : ℝ)|=(3137783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8641352851/10000000000 : ℝ)|^133 ≤ (10313328179117/12500000000000 : ℝ)^101
        have hw : |(8641352851/10000000000 : ℝ)|=(8641352851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2206768799/10000000000 : ℝ)*x 0 + (2146345317/2500000000 : ℝ)*x 1 + (-476419383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2206768799/10000000000 : ℝ)^133 ≤ (546887755287/4000000000000 : ℝ)^101 := by
    have hnat : (2206768799 : ℕ)^133*4000000000000^101 ≤ 546887755287^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206768799 10000000000 546887755287 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146345317/2500000000 : ℝ)^133 ≤ (81803620406943/100000000000000 : ℝ)^101 := by
    have hnat : (2146345317 : ℕ)^133*100000000000000^101 ≤ 81803620406943^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146345317 2500000000 81803620406943 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476419383/5000000000 : ℝ)^133 ≤ (4524185689763/100000000000000 : ℝ)^101 := by
    have hnat : (476419383 : ℕ)^133*100000000000000^101 ≤ 4524185689763^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476419383 5000000000 4524185689763 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2206768799/10000000000 : ℝ), (2146345317/2500000000 : ℝ), (-476419383/5000000000 : ℝ)] ![(546887755287/4000000000000 : ℝ), (81803620406943/100000000000000 : ℝ), (4524185689763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2206768799/10000000000 : ℝ)|^133 ≤ (546887755287/4000000000000 : ℝ)^101
        have hw : |(2206768799/10000000000 : ℝ)|=(2206768799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2146345317/2500000000 : ℝ)|^133 ≤ (81803620406943/100000000000000 : ℝ)^101
        have hw : |(2146345317/2500000000 : ℝ)|=(2146345317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-476419383/5000000000 : ℝ)|^133 ≤ (4524185689763/100000000000000 : ℝ)^101
        have hw : |(-476419383/5000000000 : ℝ)|=(476419383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2001596109/5000000000 : ℝ)*x 0 + (723085761/1000000000 : ℝ)*x 1 + (498149317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001596109/5000000000 : ℝ)^133 ≤ (468011186879/1562500000000 : ℝ)^101 := by
    have hnat : (2001596109 : ℕ)^133*1562500000000^101 ≤ 468011186879^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001596109 5000000000 468011186879 1562500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (723085761/1000000000 : ℝ)^133 ≤ (65249423640523/100000000000000 : ℝ)^101 := by
    have hnat : (723085761 : ℕ)^133*100000000000000^101 ≤ 65249423640523^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723085761 1000000000 65249423640523 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (498149317/5000000000 : ℝ)^133 ≤ (2398930188233/50000000000000 : ℝ)^101 := by
    have hnat : (498149317 : ℕ)^133*50000000000000^101 ≤ 2398930188233^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498149317 5000000000 2398930188233 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2001596109/5000000000 : ℝ), (723085761/1000000000 : ℝ), (498149317/5000000000 : ℝ)] ![(468011186879/1562500000000 : ℝ), (65249423640523/100000000000000 : ℝ), (2398930188233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2001596109/5000000000 : ℝ)|^133 ≤ (468011186879/1562500000000 : ℝ)^101
        have hw : |(2001596109/5000000000 : ℝ)|=(2001596109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(723085761/1000000000 : ℝ)|^133 ≤ (65249423640523/100000000000000 : ℝ)^101
        have hw : |(723085761/1000000000 : ℝ)|=(723085761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(498149317/5000000000 : ℝ)|^133 ≤ (2398930188233/50000000000000 : ℝ)^101
        have hw : |(498149317/5000000000 : ℝ)|=(498149317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-11069937/78125000 : ℝ)*x 0 + (4492505547/10000000000 : ℝ)*x 1 + (6569422929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11069937/78125000 : ℝ)^133 ≤ (3814587112409/50000000000000 : ℝ)^101 := by
    have hnat : (11069937 : ℕ)^133*50000000000000^101 ≤ 3814587112409^101*78125000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11069937 78125000 3814587112409 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492505547/10000000000 : ℝ)^133 ≤ (34864705990471/100000000000000 : ℝ)^101 := by
    have hnat : (4492505547 : ℕ)^133*100000000000000^101 ≤ 34864705990471^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492505547 10000000000 34864705990471 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6569422929/10000000000 : ℝ)^133 ≤ (57506119773181/100000000000000 : ℝ)^101 := by
    have hnat : (6569422929 : ℕ)^133*100000000000000^101 ≤ 57506119773181^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6569422929 10000000000 57506119773181 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11069937/78125000 : ℝ), (4492505547/10000000000 : ℝ), (6569422929/10000000000 : ℝ)] ![(3814587112409/50000000000000 : ℝ), (34864705990471/100000000000000 : ℝ), (57506119773181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11069937/78125000 : ℝ)|^133 ≤ (3814587112409/50000000000000 : ℝ)^101
        have hw : |(-11069937/78125000 : ℝ)|=(11069937/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492505547/10000000000 : ℝ)|^133 ≤ (34864705990471/100000000000000 : ℝ)^101
        have hw : |(4492505547/10000000000 : ℝ)|=(4492505547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6569422929/10000000000 : ℝ)|^133 ≤ (57506119773181/100000000000000 : ℝ)^101
        have hw : |(6569422929/10000000000 : ℝ)|=(6569422929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (175765017/1000000000 : ℝ)*x 0 + (-38905747/10000000000 : ℝ)*x 1 + (921554233/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175765017/1000000000 : ℝ)^133 ≤ (1013218509093/10000000000000 : ℝ)^101 := by
    have hnat : (175765017 : ℕ)^133*10000000000000^101 ≤ 1013218509093^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175765017 1000000000 1013218509093 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38905747/10000000000 : ℝ)^133 ≤ (67058488613/100000000000000 : ℝ)^101 := by
    have hnat : (38905747 : ℕ)^133*100000000000000^101 ≤ 67058488613^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38905747 10000000000 67058488613 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921554233/1000000000 : ℝ)^133 ≤ (44900378203023/50000000000000 : ℝ)^101 := by
    have hnat : (921554233 : ℕ)^133*50000000000000^101 ≤ 44900378203023^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921554233 1000000000 44900378203023 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(175765017/1000000000 : ℝ), (-38905747/10000000000 : ℝ), (921554233/1000000000 : ℝ)] ![(1013218509093/10000000000000 : ℝ), (67058488613/100000000000000 : ℝ), (44900378203023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(175765017/1000000000 : ℝ)|^133 ≤ (1013218509093/10000000000000 : ℝ)^101
        have hw : |(175765017/1000000000 : ℝ)|=(175765017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38905747/10000000000 : ℝ)|^133 ≤ (67058488613/100000000000000 : ℝ)^101
        have hw : |(-38905747/10000000000 : ℝ)|=(38905747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(921554233/1000000000 : ℝ)|^133 ≤ (44900378203023/50000000000000 : ℝ)^101
        have hw : |(921554233/1000000000 : ℝ)|=(921554233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (185703801/250000000 : ℝ)*x 0 + (3861050767/10000000000 : ℝ)*x 1 + (-168121869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (185703801/250000000 : ℝ)^133 ≤ (67603896144703/100000000000000 : ℝ)^101 := by
    have hnat : (185703801 : ℕ)^133*100000000000000^101 ≤ 67603896144703^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185703801 250000000 67603896144703 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3861050767/10000000000 : ℝ)^133 ≤ (5712033151843/20000000000000 : ℝ)^101 := by
    have hnat : (3861050767 : ℕ)^133*20000000000000^101 ≤ 5712033151843^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3861050767 10000000000 5712033151843 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168121869/2000000000 : ℝ)^133 ≤ (3835938081969/100000000000000 : ℝ)^101 := by
    have hnat : (168121869 : ℕ)^133*100000000000000^101 ≤ 3835938081969^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168121869 2000000000 3835938081969 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(185703801/250000000 : ℝ), (3861050767/10000000000 : ℝ), (-168121869/2000000000 : ℝ)] ![(67603896144703/100000000000000 : ℝ), (5712033151843/20000000000000 : ℝ), (3835938081969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(185703801/250000000 : ℝ)|^133 ≤ (67603896144703/100000000000000 : ℝ)^101
        have hw : |(185703801/250000000 : ℝ)|=(185703801/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3861050767/10000000000 : ℝ)|^133 ≤ (5712033151843/20000000000000 : ℝ)^101
        have hw : |(3861050767/10000000000 : ℝ)|=(3861050767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168121869/2000000000 : ℝ)|^133 ≤ (3835938081969/100000000000000 : ℝ)^101
        have hw : |(-168121869/2000000000 : ℝ)|=(168121869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4404459923/5000000000 : ℝ)*x 0 + (1944207217/10000000000 : ℝ)*x 1 + (6531573/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4404459923/5000000000 : ℝ)^133 ≤ (16923976244561/20000000000000 : ℝ)^101 := by
    have hnat : (4404459923 : ℕ)^133*20000000000000^101 ≤ 16923976244561^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404459923 5000000000 16923976244561 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944207217/10000000000 : ℝ)^133 ≤ (1157160648409/10000000000000 : ℝ)^101 := by
    have hnat : (1944207217 : ℕ)^133*10000000000000^101 ≤ 1157160648409^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944207217 10000000000 1157160648409 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6531573/78125000 : ℝ)^133 ≤ (1904256139807/50000000000000 : ℝ)^101 := by
    have hnat : (6531573 : ℕ)^133*50000000000000^101 ≤ 1904256139807^101*78125000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6531573 78125000 1904256139807 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4404459923/5000000000 : ℝ), (1944207217/10000000000 : ℝ), (6531573/78125000 : ℝ)] ![(16923976244561/20000000000000 : ℝ), (1157160648409/10000000000000 : ℝ), (1904256139807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4404459923/5000000000 : ℝ)|^133 ≤ (16923976244561/20000000000000 : ℝ)^101
        have hw : |(4404459923/5000000000 : ℝ)|=(4404459923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1944207217/10000000000 : ℝ)|^133 ≤ (1157160648409/10000000000000 : ℝ)^101
        have hw : |(1944207217/10000000000 : ℝ)|=(1944207217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6531573/78125000 : ℝ)|^133 ≤ (1904256139807/50000000000000 : ℝ)^101
        have hw : |(6531573/78125000 : ℝ)|=(6531573/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-230261043/2000000000 : ℝ)*x 0 + (4150494507/5000000000 : ℝ)*x 1 + (2479722791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230261043/2000000000 : ℝ)^133 ≤ (5804246776951/100000000000000 : ℝ)^101 := by
    have hnat : (230261043 : ℕ)^133*100000000000000^101 ≤ 5804246776951^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230261043 2000000000 5804246776951 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4150494507/5000000000 : ℝ)^133 ≤ (611360872639/781250000000 : ℝ)^101 := by
    have hnat : (4150494507 : ℕ)^133*781250000000^101 ≤ 611360872639^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150494507 5000000000 611360872639 781250000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2479722791/10000000000 : ℝ)^133 ≤ (7970780753337/50000000000000 : ℝ)^101 := by
    have hnat : (2479722791 : ℕ)^133*50000000000000^101 ≤ 7970780753337^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2479722791 10000000000 7970780753337 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230261043/2000000000 : ℝ), (4150494507/5000000000 : ℝ), (2479722791/10000000000 : ℝ)] ![(5804246776951/100000000000000 : ℝ), (611360872639/781250000000 : ℝ), (7970780753337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230261043/2000000000 : ℝ)|^133 ≤ (5804246776951/100000000000000 : ℝ)^101
        have hw : |(-230261043/2000000000 : ℝ)|=(230261043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4150494507/5000000000 : ℝ)|^133 ≤ (611360872639/781250000000 : ℝ)^101
        have hw : |(4150494507/5000000000 : ℝ)|=(4150494507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2479722791/10000000000 : ℝ)|^133 ≤ (7970780753337/50000000000000 : ℝ)^101
        have hw : |(2479722791/10000000000 : ℝ)|=(2479722791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1850248711/2500000000 : ℝ)*x 0 + (-3613549/5000000000 : ℝ)*x 1 + (1070114419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1850248711/2500000000 : ℝ)^133 ≤ (33639309209671/50000000000000 : ℝ)^101 := by
    have hnat : (1850248711 : ℕ)^133*50000000000000^101 ≤ 33639309209671^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850248711 2500000000 33639309209671 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3613549/5000000000 : ℝ)^133 ≤ (3653879389/50000000000000 : ℝ)^101 := by
    have hnat : (3613549 : ℕ)^133*50000000000000^101 ≤ 3653879389^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3613549 5000000000 3653879389 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1070114419/2500000000 : ℝ)^133 ≤ (1308562952717/4000000000000 : ℝ)^101 := by
    have hnat : (1070114419 : ℕ)^133*4000000000000^101 ≤ 1308562952717^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070114419 2500000000 1308562952717 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1850248711/2500000000 : ℝ), (-3613549/5000000000 : ℝ), (1070114419/2500000000 : ℝ)] ![(33639309209671/50000000000000 : ℝ), (3653879389/50000000000000 : ℝ), (1308562952717/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1850248711/2500000000 : ℝ)|^133 ≤ (33639309209671/50000000000000 : ℝ)^101
        have hw : |(1850248711/2500000000 : ℝ)|=(1850248711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3613549/5000000000 : ℝ)|^133 ≤ (3653879389/50000000000000 : ℝ)^101
        have hw : |(-3613549/5000000000 : ℝ)|=(3613549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1070114419/2500000000 : ℝ)|^133 ≤ (1308562952717/4000000000000 : ℝ)^101
        have hw : |(1070114419/2500000000 : ℝ)|=(1070114419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (9411979/62500000 : ℝ)*x 0 + (2170534117/2500000000 : ℝ)*x 1 + (-783747673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9411979/62500000 : ℝ)^133 ≤ (330645189743/4000000000000 : ℝ)^101 := by
    have hnat : (9411979 : ℕ)^133*4000000000000^101 ≤ 330645189743^101*62500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9411979 62500000 330645189743 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170534117/2500000000 : ℝ)^133 ≤ (41509889484901/50000000000000 : ℝ)^101 := by
    have hnat : (2170534117 : ℕ)^133*50000000000000^101 ≤ 41509889484901^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170534117 2500000000 41509889484901 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (783747673/5000000000 : ℝ)^133 ≤ (1742818255887/20000000000000 : ℝ)^101 := by
    have hnat : (783747673 : ℕ)^133*20000000000000^101 ≤ 1742818255887^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783747673 5000000000 1742818255887 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9411979/62500000 : ℝ), (2170534117/2500000000 : ℝ), (-783747673/5000000000 : ℝ)] ![(330645189743/4000000000000 : ℝ), (41509889484901/50000000000000 : ℝ), (1742818255887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9411979/62500000 : ℝ)|^133 ≤ (330645189743/4000000000000 : ℝ)^101
        have hw : |(9411979/62500000 : ℝ)|=(9411979/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2170534117/2500000000 : ℝ)|^133 ≤ (41509889484901/50000000000000 : ℝ)^101
        have hw : |(2170534117/2500000000 : ℝ)|=(2170534117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-783747673/5000000000 : ℝ)|^133 ≤ (1742818255887/20000000000000 : ℝ)^101
        have hw : |(-783747673/5000000000 : ℝ)|=(783747673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s3_s3_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4229065627/5000000000 : ℝ)*x 0 + (1031869953/5000000000 : ℝ)*x 1 + (170781913/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4229065627/5000000000 : ℝ)^133 ≤ (802107639033/1000000000000 : ℝ)^101 := by
    have hnat : (4229065627 : ℕ)^133*1000000000000^101 ≤ 802107639033^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229065627 5000000000 802107639033 1000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031869953/5000000000 : ℝ)^133 ≤ (6258726078813/50000000000000 : ℝ)^101 := by
    have hnat : (1031869953 : ℕ)^133*50000000000000^101 ≤ 6258726078813^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031869953 5000000000 6258726078813 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170781913/1250000000 : ℝ)^133 ≤ (1817945980031/25000000000000 : ℝ)^101 := by
    have hnat : (170781913 : ℕ)^133*25000000000000^101 ≤ 1817945980031^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170781913 1250000000 1817945980031 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4229065627/5000000000 : ℝ), (1031869953/5000000000 : ℝ), (170781913/1250000000 : ℝ)] ![(802107639033/1000000000000 : ℝ), (6258726078813/50000000000000 : ℝ), (1817945980031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4229065627/5000000000 : ℝ)|^133 ≤ (802107639033/1000000000000 : ℝ)^101
        have hw : |(4229065627/5000000000 : ℝ)|=(4229065627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031869953/5000000000 : ℝ)|^133 ≤ (6258726078813/50000000000000 : ℝ)^101
        have hw : |(1031869953/5000000000 : ℝ)|=(1031869953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170781913/1250000000 : ℝ)|^133 ≤ (1817945980031/25000000000000 : ℝ)^101
        have hw : |(170781913/1250000000 : ℝ)|=(170781913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304055_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((22179/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22179/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17651/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17651/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10991/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10991/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2624/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2624/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20701/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20701/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20779/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20779/25000 : ℝ)*X 1 2) := by
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
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s3_pow0 : (22179/25000 : ℝ) ^ (33/8 : ℝ) ≤ (15256259306397941311/25000000000000000000 : ℝ) := by
    have hpowers : (22179/25000 : ℝ)^33 ≤ (15256259306397941311/25000000000000000000 : ℝ)^8 := by
      have hnat : (22179 : ℕ)^33*25000000000000000000^8 ≤ 15256259306397941311^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22179 25000 15256259306397941311 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22179/25000 : ℝ)) (X := (15256259306397941311/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (40256259306397941311/25000000000000000000 : ℝ) ≤ (448968600759969/400000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (40256259306397941311/25000000000000000000 : ℝ)^8 ≤ (448968600759969/400000000000000 : ℝ)^33 := by
      have hnat : (40256259306397941311 : ℕ)^8*400000000000000^33 ≤ 448968600759969^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40256259306397941311 25000000000000000000 448968600759969 400000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (448968600759969/400000000000000 : ℝ)) (X := (40256259306397941311/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (27756259306397941311/12500000000000000000 : ℝ) ≤ (6066778051682433/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (27756259306397941311/12500000000000000000 : ℝ)^8 ≤ (6066778051682433/5000000000000000 : ℝ)^33 := by
      have hnat : (27756259306397941311 : ℕ)^8*5000000000000000^33 ≤ 6066778051682433^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27756259306397941311 12500000000000000000 6066778051682433 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6066778051682433/5000000000000000 : ℝ)) (X := (27756259306397941311/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(48968600759969/354864000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(303113694788547/2957200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (22179/25000 : ℝ)) (alpha := (48968600759969/354864000000000 : ℝ)) (beta := (303113694788547/2957200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22179/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(48968600759969/354864000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(303113694788547/2957200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (17651/20000 : ℝ) ^ (33/8 : ℝ) ≤ (29863774416348451689/50000000000000000000 : ℝ) := by
    have hpowers : (17651/20000 : ℝ)^33 ≤ (29863774416348451689/50000000000000000000 : ℝ)^8 := by
      have hnat : (17651 : ℕ)^33*50000000000000000000^8 ≤ 29863774416348451689^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17651 20000 29863774416348451689 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17651/20000 : ℝ)) (X := (29863774416348451689/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (79863774416348451689/50000000000000000000 : ℝ) ≤ (11202222656507599/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (79863774416348451689/50000000000000000000 : ℝ)^8 ≤ (11202222656507599/10000000000000000 : ℝ)^33 := by
      have hnat : (79863774416348451689 : ℕ)^8*10000000000000000^33 ≤ 11202222656507599^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79863774416348451689 50000000000000000000 11202222656507599 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11202222656507599/10000000000000000 : ℝ)) (X := (79863774416348451689/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (54863774416348451689/25000000000000000000 : ℝ) ≤ (1512378446000427/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (54863774416348451689/25000000000000000000 : ℝ)^8 ≤ (1512378446000427/1250000000000000 : ℝ)^33 := by
      have hnat : (54863774416348451689 : ℕ)^8*1250000000000000^33 ≤ 1512378446000427^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54863774416348451689 25000000000000000000 1512378446000427 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1512378446000427/1250000000000000 : ℝ)) (X := (54863774416348451689/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1202222656507599/8825500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(896804911495817/8825500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (17651/20000 : ℝ)) (alpha := (1202222656507599/8825500000000000 : ℝ)) (beta := (896804911495817/8825500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (17651/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1202222656507599/8825500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(896804911495817/8825500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (10991/12500 : ℝ) ^ (33/8 : ℝ) ≤ (58819953764474083651/100000000000000000000 : ℝ) := by
    have hpowers : (10991/12500 : ℝ)^33 ≤ (58819953764474083651/100000000000000000000 : ℝ)^8 := by
      have hnat : (10991 : ℕ)^33*100000000000000000000^8 ≤ 58819953764474083651^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10991 12500 58819953764474083651 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10991/12500 : ℝ)) (X := (58819953764474083651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (158819953764474083651/100000000000000000000 : ℝ) ≤ (11186758387188141/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (158819953764474083651/100000000000000000000 : ℝ)^8 ≤ (11186758387188141/10000000000000000 : ℝ)^33 := by
      have hnat : (158819953764474083651 : ℕ)^8*10000000000000000^33 ≤ 11186758387188141^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        158819953764474083651 100000000000000000000 11186758387188141 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11186758387188141/10000000000000000 : ℝ)) (X := (158819953764474083651/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (108819953764474083651/50000000000000000000 : ℝ) ≤ (6037345253543409/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (108819953764474083651/50000000000000000000 : ℝ)^8 ≤ (6037345253543409/5000000000000000 : ℝ)^33 := by
      have hnat : (108819953764474083651 : ℕ)^8*5000000000000000^33 ≤ 6037345253543409^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108819953764474083651 50000000000000000000 6037345253543409 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6037345253543409/5000000000000000 : ℝ)) (X := (108819953764474083651/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1186758387188141/8792800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(887932119898677/8792800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (10991/12500 : ℝ)) (alpha := (1186758387188141/8792800000000000 : ℝ)) (beta := (887932119898677/8792800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (10991/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1186758387188141/8792800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(887932119898677/8792800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-29295161/250000000 : ℝ)*X 0 0+(6034986699/10000000000 : ℝ)*X 0 1+(5233921391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((826877473/1250000000 : ℝ)*X 0 0+(476763571/1250000000 : ℝ)*X 0 1+(1115113723/5000000000 : ℝ)*X 0 2+(826877473/1250000000 : ℝ)*X 1 0+(476763571/1250000000 : ℝ)*X 1 1+(1115113723/5000000000 : ℝ)*X 1 2+(826877473/1250000000 : ℝ)*X 2 0+(476763571/1250000000 : ℝ)*X 2 1+(1115113723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-2881770091/10000000000 : ℝ)*X 0 0+(1060849003/2500000000 : ℝ)*X 0 1+(5747830057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((665066289/2500000000 : ℝ)*X 1 0+(3137783/5000000000 : ℝ)*X 1 1+(8641352851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((2206768799/10000000000 : ℝ)*X 2 0+(2146345317/2500000000 : ℝ)*X 2 1+(-476419383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2001596109/5000000000 : ℝ)*X 0 0+(723085761/1000000000 : ℝ)*X 0 1+(498149317/5000000000 : ℝ)*X 0 2+(2001596109/5000000000 : ℝ)*X 1 0+(723085761/1000000000 : ℝ)*X 1 1+(498149317/5000000000 : ℝ)*X 1 2+(2001596109/5000000000 : ℝ)*X 2 0+(723085761/1000000000 : ℝ)*X 2 1+(498149317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-11069937/78125000 : ℝ)*X 0 0+(4492505547/10000000000 : ℝ)*X 0 1+(6569422929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((175765017/1000000000 : ℝ)*X 1 0+(-38905747/10000000000 : ℝ)*X 1 1+(921554233/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((185703801/250000000 : ℝ)*X 2 0+(3861050767/10000000000 : ℝ)*X 2 1+(-168121869/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((4404459923/5000000000 : ℝ)*X 0 0+(1944207217/10000000000 : ℝ)*X 0 1+(6531573/78125000 : ℝ)*X 0 2+(4404459923/5000000000 : ℝ)*X 1 0+(1944207217/10000000000 : ℝ)*X 1 1+(6531573/78125000 : ℝ)*X 1 2+(4404459923/5000000000 : ℝ)*X 2 0+(1944207217/10000000000 : ℝ)*X 2 1+(6531573/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-230261043/2000000000 : ℝ)*X 0 0+(4150494507/5000000000 : ℝ)*X 0 1+(2479722791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((1850248711/2500000000 : ℝ)*X 1 0+(-3613549/5000000000 : ℝ)*X 1 1+(1070114419/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((9411979/62500000 : ℝ)*X 2 0+(2170534117/2500000000 : ℝ)*X 2 1+(-783747673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((4229065627/5000000000 : ℝ)*X 0 0+(1031869953/5000000000 : ℝ)*X 0 1+(170781913/1250000000 : ℝ)*X 0 2+(4229065627/5000000000 : ℝ)*X 1 0+(1031869953/5000000000 : ℝ)*X 1 1+(170781913/1250000000 : ℝ)*X 1 2+(4229065627/5000000000 : ℝ)*X 2 0+(1031869953/5000000000 : ℝ)*X 2 1+(170781913/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((2624/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2624/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2517506101227026938945619847/388004282000000000000000000000000 : ℝ) := by norm_num
    linear_combination (701741132333/1000000000000 : ℝ)*(base7) + (17629/1000000000000 : ℝ)*(base40) + (167941/200000000000 : ℝ)*(base49) + (688786764581/1000000000000 : ℝ)*(base53) + (451877/1000000000000 : ℝ)*(base60) + (443962837867/250000000000 : ℝ)*(major_s3_0) + (443962837867/250000000000 : ℝ)*(major_s3_1) + (1087064586887/1000000000000 : ℝ)*(major_s3_2) + (13374129/1000000000000 : ℝ)*(sp_s3_0) + (626355751247/500000000000 : ℝ)*(sp_s3_7) + (1252724876623/1000000000000 : ℝ)*(sp_s3_8) + (485376342241/250000000000 : ℝ)*(sp_s3_9) + (23407387007/12500000000 : ℝ)*(sp_s3_13) + (78403/12500000000 : ℝ)*(sp_s3_23) + (1170849828227/1000000000000 : ℝ)*(f.failure) + (485377910301/250000000000 : ℝ)*(f.sum) + (156629132463326612219/776008564000000000000000000000000 : ℝ)*base62 + (1476724269768221/8792800000000000000000000000 : ℝ)*base64 + (45275326253147/4412750000000000000000000000 : ℝ)*base67 + (4662786130739973/8792800000000000000000000000 : ℝ)*base68 + (64462750001658693761/195015511200000000000000000000000 : ℝ)*base71 + (561636291847841/739300000000000000000000000 : ℝ)*base72 + (643187174140117/2206375000000000000000000000 : ℝ)*base74 + (141899368542761/443580000000000000000000000 : ℝ)*base76 + (9853078474483373187/65246921500000000000000000000000 : ℝ)*base79 + (5693/12500000000000000 : ℝ)*base87 + (5693/12500000000000000 : ℝ)*base89 + (5693/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20701/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20701/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2152915513994100906925453751361/179282228551625000000000000000000000 : ℝ) := by norm_num
    linear_combination (346690982681/500000000000 : ℝ)*(base7) + (157171/200000000000 : ℝ)*(base34) + (371503/200000000000 : ℝ)*(base40) + (485806213371/1000000000000 : ℝ)*(base53) + (403948055211/250000000000 : ℝ)*(major_s3_0) + (1615793006699/1000000000000 : ℝ)*(major_s3_1) + (70624174583/62500000000 : ℝ)*(major_s3_2) + (11287659/125000000000 : ℝ)*(sp_s3_0) + (413349/8000000000 : ℝ)*(sp_s3_7) + (82335813/500000000000 : ℝ)*(sp_s3_8) + (1246206829803/1000000000000 : ℝ)*(sp_s3_14) + (1246184913929/1000000000000 : ℝ)*(sp_s3_15) + (866077899463/500000000000 : ℝ)*(sp_s3_16) + (21983771801/12500000000 : ℝ)*(sp_s3_20) + (1065320564573/1000000000000 : ℝ)*(f.failure) + (866077899463/500000000000 : ℝ)*(f.sum) + (18518085046398053629/97001070500000000000000000000000 : ℝ)*base62 + (450833810751/137387500000000000000000000 : ℝ)*base64 + (1961989695517717/8825500000000000000000000000 : ℝ)*base67 + (24942681787173/549550000000000000000000000 : ℝ)*base69 + (2501228348857237489/8125646300000000000000000000000 : ℝ)*base70 + (565998512551537/739300000000000000000000000 : ℝ)*base73 + (2579012329969701/8825500000000000000000000000 : ℝ)*base75 + (21223209206407/147860000000000000000000000 : ℝ)*base76 + (1176774582629754201/4077932593750000000000000000000 : ℝ)*base79 + (2007/12500000000000000 : ℝ)*base87 + (2007/12500000000000000 : ℝ)*base89 + (2007/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20779/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20779/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22942940353202701631379491591437/1434257828413000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103425744903/125000000000 : ℝ)*(base7) + (91035460507/1000000000000 : ℝ)*(base43) + (329480502011/200000000000 : ℝ)*(major_s3_0) + (389091762387/250000000000 : ℝ)*(major_s3_1) + (329480502011/200000000000 : ℝ)*(major_s3_2) + (3393329/1000000000000 : ℝ)*(sp_s3_0) + (4985183/250000000000 : ℝ)*(sp_s3_6) + (212879/250000000000 : ℝ)*(sp_s3_7) + (51853711/500000000000 : ℝ)*(sp_s3_9) + (128515233/1000000000000 : ℝ)*(sp_s3_20) + (319916934247/200000000000 : ℝ)*(sp_s3_21) + (1690624376587/1000000000000 : ℝ)*(sp_s3_22) + (799742604329/500000000000 : ℝ)*(sp_s3_23) + (1913418765757/1000000000000 : ℝ)*(sp_s3_27) + (1086161262497/1000000000000 : ℝ)*(f.failure) + (1690624376587/1000000000000 : ℝ)*(f.sum) + (339761827620763779819/776008564000000000000000000000000 : ℝ)*base62 + (157393187549109/351712000000000000000000000 : ℝ)*base64 + (65495703741221/2206375000000000000000000000 : ℝ)*base67 + (872575139709921/1758560000000000000000000000 : ℝ)*base68 + (6449450790148605809/39003102240000000000000000000000 : ℝ)*base70 + (99385306009199/591440000000000000000000000 : ℝ)*base72 + (174277589258053/551593750000000000000000000 : ℝ)*base74 + (733416096532133/1774320000000000000000000000 : ℝ)*base76 + (22463377869992327077/260987686000000000000000000000000 : ℝ)*base78 + (6877/12500000000000000 : ℝ)*base86 + (6877/12500000000000000 : ℝ)*base88 + (6877/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((22179/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22179/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17651/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17651/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10991/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10991/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2624/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2624/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20701/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20701/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20779/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20779/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304055_s3 p hpa hpb X hX hprev2

#print axioms solution

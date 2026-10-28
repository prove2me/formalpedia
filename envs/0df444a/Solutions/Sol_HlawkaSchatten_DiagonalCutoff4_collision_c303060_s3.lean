-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c303060_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:57:07.737881+00:00
-- url     : https://prove2.me/submissions/32c24e7c-e271-4cb3-9f25-53859c9db327

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
theorem collision_support_c303060_s3_s3_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073461567/10000000000 : ℝ)*x 0 + (430448237/1000000000 : ℝ)*x 1 + (-6322651697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073461567/10000000000 : ℝ)^33 ≤ (6266264331883/50000000000000 : ℝ)^25 := by
    have hnat : (2073461567 : ℕ)^33*50000000000000^25 ≤ 6266264331883^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073461567 10000000000 6266264331883 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430448237/1000000000 : ℝ)^33 ≤ (3286817813869/10000000000000 : ℝ)^25 := by
    have hnat : (430448237 : ℕ)^33*10000000000000^25 ≤ 3286817813869^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430448237 1000000000 3286817813869 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6322651697/10000000000 : ℝ)^33 ≤ (54599293182979/100000000000000 : ℝ)^25 := by
    have hnat : (6322651697 : ℕ)^33*100000000000000^25 ≤ 54599293182979^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6322651697 10000000000 54599293182979 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073461567/10000000000 : ℝ), (430448237/1000000000 : ℝ), (-6322651697/10000000000 : ℝ)] ![(6266264331883/50000000000000 : ℝ), (3286817813869/10000000000000 : ℝ), (54599293182979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073461567/10000000000 : ℝ)|^33 ≤ (6266264331883/50000000000000 : ℝ)^25
        have hw : |(-2073461567/10000000000 : ℝ)|=(2073461567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(430448237/1000000000 : ℝ)|^33 ≤ (3286817813869/10000000000000 : ℝ)^25
        have hw : |(430448237/1000000000 : ℝ)|=(430448237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6322651697/10000000000 : ℝ)|^33 ≤ (54599293182979/100000000000000 : ℝ)^25
        have hw : |(-6322651697/10000000000 : ℝ)|=(6322651697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2245143629/5000000000 : ℝ)*x 0 + (-2282923171/10000000000 : ℝ)*x 1 + (-3002867863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245143629/5000000000 : ℝ)^33 ≤ (17376881898723/50000000000000 : ℝ)^25 := by
    have hnat : (2245143629 : ℕ)^33*50000000000000^25 ≤ 17376881898723^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245143629 5000000000 17376881898723 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282923171/10000000000 : ℝ)^33 ≤ (14230118309447/100000000000000 : ℝ)^25 := by
    have hnat : (2282923171 : ℕ)^33*100000000000000^25 ≤ 14230118309447^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282923171 10000000000 14230118309447 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3002867863/5000000000 : ℝ)^33 ≤ (51016117876073/100000000000000 : ℝ)^25 := by
    have hnat : (3002867863 : ℕ)^33*100000000000000^25 ≤ 51016117876073^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3002867863 5000000000 51016117876073 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245143629/5000000000 : ℝ), (-2282923171/10000000000 : ℝ), (-3002867863/5000000000 : ℝ)] ![(17376881898723/50000000000000 : ℝ), (14230118309447/100000000000000 : ℝ), (51016117876073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245143629/5000000000 : ℝ)|^33 ≤ (17376881898723/50000000000000 : ℝ)^25
        have hw : |(2245143629/5000000000 : ℝ)|=(2245143629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282923171/10000000000 : ℝ)|^33 ≤ (14230118309447/100000000000000 : ℝ)^25
        have hw : |(-2282923171/10000000000 : ℝ)|=(2282923171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3002867863/5000000000 : ℝ)|^33 ≤ (51016117876073/100000000000000 : ℝ)^25
        have hw : |(-3002867863/5000000000 : ℝ)|=(3002867863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2367773257/5000000000 : ℝ)*x 0 + (2992762829/5000000000 : ℝ)*x 1 + (1997402209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2367773257/5000000000 : ℝ)^33 ≤ (3728108479939/10000000000000 : ℝ)^25 := by
    have hnat : (2367773257 : ℕ)^33*10000000000000^25 ≤ 3728108479939^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2367773257 5000000000 3728108479939 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2992762829/5000000000 : ℝ)^33 ≤ (2539481399301/5000000000000 : ℝ)^25 := by
    have hnat : (2992762829 : ℕ)^33*5000000000000^25 ≤ 2539481399301^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2992762829 5000000000 2539481399301 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997402209/10000000000 : ℝ)^33 ≤ (5964643595543/50000000000000 : ℝ)^25 := by
    have hnat : (1997402209 : ℕ)^33*50000000000000^25 ≤ 5964643595543^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997402209 10000000000 5964643595543 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2367773257/5000000000 : ℝ), (2992762829/5000000000 : ℝ), (1997402209/10000000000 : ℝ)] ![(3728108479939/10000000000000 : ℝ), (2539481399301/5000000000000 : ℝ), (5964643595543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2367773257/5000000000 : ℝ)|^33 ≤ (3728108479939/10000000000000 : ℝ)^25
        have hw : |(2367773257/5000000000 : ℝ)|=(2367773257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2992762829/5000000000 : ℝ)|^33 ≤ (2539481399301/5000000000000 : ℝ)^25
        have hw : |(2992762829/5000000000 : ℝ)|=(2992762829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1997402209/10000000000 : ℝ)|^33 ≤ (5964643595543/50000000000000 : ℝ)^25
        have hw : |(1997402209/10000000000 : ℝ)|=(1997402209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1852422759/10000000000 : ℝ)*x 0 + (3624701847/10000000000 : ℝ)*x 1 + (-3523511101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1852422759/10000000000 : ℝ)^33 ≤ (10799830582217/100000000000000 : ℝ)^25 := by
    have hnat : (1852422759 : ℕ)^33*100000000000000^25 ≤ 10799830582217^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852422759 10000000000 10799830582217 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3624701847/10000000000 : ℝ)^33 ≤ (13098133903677/50000000000000 : ℝ)^25 := by
    have hnat : (3624701847 : ℕ)^33*50000000000000^25 ≤ 13098133903677^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3624701847 10000000000 13098133903677 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3523511101/5000000000 : ℝ)^33 ≤ (7875487698991/12500000000000 : ℝ)^25 := by
    have hnat : (3523511101 : ℕ)^33*12500000000000^25 ≤ 7875487698991^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3523511101 5000000000 7875487698991 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1852422759/10000000000 : ℝ), (3624701847/10000000000 : ℝ), (-3523511101/5000000000 : ℝ)] ![(10799830582217/100000000000000 : ℝ), (13098133903677/50000000000000 : ℝ), (7875487698991/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1852422759/10000000000 : ℝ)|^33 ≤ (10799830582217/100000000000000 : ℝ)^25
        have hw : |(-1852422759/10000000000 : ℝ)|=(1852422759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3624701847/10000000000 : ℝ)|^33 ≤ (13098133903677/50000000000000 : ℝ)^25
        have hw : |(3624701847/10000000000 : ℝ)|=(3624701847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3523511101/5000000000 : ℝ)|^33 ≤ (7875487698991/12500000000000 : ℝ)^25
        have hw : |(-3523511101/5000000000 : ℝ)|=(3523511101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (973272791/2500000000 : ℝ)*x 0 + (-296108967/2000000000 : ℝ)*x 1 + (-176546453/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (973272791/2500000000 : ℝ)^33 ≤ (28786498192441/100000000000000 : ℝ)^25 := by
    have hnat : (973272791 : ℕ)^33*100000000000000^25 ≤ 28786498192441^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973272791 2500000000 28786498192441 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296108967/2000000000 : ℝ)^33 ≤ (160689115259/2000000000000 : ℝ)^25 := by
    have hnat : (296108967 : ℕ)^33*2000000000000^25 ≤ 160689115259^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296108967 2000000000 160689115259 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176546453/250000000 : ℝ)^33 ≤ (12635809206403/20000000000000 : ℝ)^25 := by
    have hnat : (176546453 : ℕ)^33*20000000000000^25 ≤ 12635809206403^25*250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176546453 250000000 12635809206403 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(973272791/2500000000 : ℝ), (-296108967/2000000000 : ℝ), (-176546453/250000000 : ℝ)] ![(28786498192441/100000000000000 : ℝ), (160689115259/2000000000000 : ℝ), (12635809206403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(973272791/2500000000 : ℝ)|^33 ≤ (28786498192441/100000000000000 : ℝ)^25
        have hw : |(973272791/2500000000 : ℝ)|=(973272791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-296108967/2000000000 : ℝ)|^33 ≤ (160689115259/2000000000000 : ℝ)^25
        have hw : |(-296108967/2000000000 : ℝ)|=(296108967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-176546453/250000000 : ℝ)|^33 ≤ (12635809206403/20000000000000 : ℝ)^25
        have hw : |(-176546453/250000000 : ℝ)|=(176546453/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (207517041/500000000 : ℝ)*x 0 + (6934900553/10000000000 : ℝ)*x 1 + (266530367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207517041/500000000 : ℝ)^33 ≤ (3915440048257/12500000000000 : ℝ)^25 := by
    have hnat : (207517041 : ℕ)^33*12500000000000^25 ≤ 3915440048257^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207517041 500000000 3915440048257 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6934900553/10000000000 : ℝ)^33 ≤ (61684083116057/100000000000000 : ℝ)^25 := by
    have hnat : (6934900553 : ℕ)^33*100000000000000^25 ≤ 61684083116057^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6934900553 10000000000 61684083116057 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266530367/2000000000 : ℝ)^33 ≤ (6992396490413/100000000000000 : ℝ)^25 := by
    have hnat : (266530367 : ℕ)^33*100000000000000^25 ≤ 6992396490413^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266530367 2000000000 6992396490413 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207517041/500000000 : ℝ), (6934900553/10000000000 : ℝ), (266530367/2000000000 : ℝ)] ![(3915440048257/12500000000000 : ℝ), (61684083116057/100000000000000 : ℝ), (6992396490413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207517041/500000000 : ℝ)|^33 ≤ (3915440048257/12500000000000 : ℝ)^25
        have hw : |(207517041/500000000 : ℝ)|=(207517041/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6934900553/10000000000 : ℝ)|^33 ≤ (61684083116057/100000000000000 : ℝ)^25
        have hw : |(6934900553/10000000000 : ℝ)|=(6934900553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(266530367/2000000000 : ℝ)|^33 ≤ (6992396490413/100000000000000 : ℝ)^25
        have hw : |(266530367/2000000000 : ℝ)|=(266530367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2897618237/5000000000 : ℝ)*x 0 + (3016381199/5000000000 : ℝ)*x 1 + (-5166539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2897618237/5000000000 : ℝ)^33 ≤ (24334584661367/50000000000000 : ℝ)^25 := by
    have hnat : (2897618237 : ℕ)^33*50000000000000^25 ≤ 24334584661367^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2897618237 5000000000 24334584661367 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3016381199/5000000000 : ℝ)^33 ≤ (25659690625301/50000000000000 : ℝ)^25 := by
    have hnat : (3016381199 : ℕ)^33*50000000000000^25 ≤ 25659690625301^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016381199 5000000000 25659690625301 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5166539/5000000000 : ℝ)^33 ≤ (1144941281/10000000000000 : ℝ)^25 := by
    have hnat : (5166539 : ℕ)^33*10000000000000^25 ≤ 1144941281^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166539 5000000000 1144941281 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2897618237/5000000000 : ℝ), (3016381199/5000000000 : ℝ), (-5166539/5000000000 : ℝ)] ![(24334584661367/50000000000000 : ℝ), (25659690625301/50000000000000 : ℝ), (1144941281/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2897618237/5000000000 : ℝ)|^33 ≤ (24334584661367/50000000000000 : ℝ)^25
        have hw : |(2897618237/5000000000 : ℝ)|=(2897618237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3016381199/5000000000 : ℝ)|^33 ≤ (25659690625301/50000000000000 : ℝ)^25
        have hw : |(3016381199/5000000000 : ℝ)|=(3016381199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5166539/5000000000 : ℝ)|^33 ≤ (1144941281/10000000000000 : ℝ)^25
        have hw : |(-5166539/5000000000 : ℝ)|=(5166539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1338592827/10000000000 : ℝ)*x 0 + (1880162417/5000000000 : ℝ)*x 1 + (-453431203/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338592827/10000000000 : ℝ)^33 ≤ (7033573195867/100000000000000 : ℝ)^25 := by
    have hnat : (1338592827 : ℕ)^33*100000000000000^25 ≤ 7033573195867^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338592827 10000000000 7033573195867 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1880162417/5000000000 : ℝ)^33 ≤ (27497770249497/100000000000000 : ℝ)^25 := by
    have hnat : (1880162417 : ℕ)^33*100000000000000^25 ≤ 27497770249497^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880162417 5000000000 27497770249497 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453431203/625000000 : ℝ)^33 ≤ (65468656533321/100000000000000 : ℝ)^25 := by
    have hnat : (453431203 : ℕ)^33*100000000000000^25 ≤ 65468656533321^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453431203 625000000 65468656533321 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1338592827/10000000000 : ℝ), (1880162417/5000000000 : ℝ), (-453431203/625000000 : ℝ)] ![(7033573195867/100000000000000 : ℝ), (27497770249497/100000000000000 : ℝ), (65468656533321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1338592827/10000000000 : ℝ)|^33 ≤ (7033573195867/100000000000000 : ℝ)^25
        have hw : |(-1338592827/10000000000 : ℝ)|=(1338592827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1880162417/5000000000 : ℝ)|^33 ≤ (27497770249497/100000000000000 : ℝ)^25
        have hw : |(1880162417/5000000000 : ℝ)|=(1880162417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-453431203/625000000 : ℝ)|^33 ≤ (65468656533321/100000000000000 : ℝ)^25
        have hw : |(-453431203/625000000 : ℝ)|=(453431203/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3389338509/10000000000 : ℝ)*x 0 + (-224608109/1250000000 : ℝ)*x 1 + (-3635102779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3389338509/10000000000 : ℝ)^33 ≤ (5993654950993/25000000000000 : ℝ)^25 := by
    have hnat : (3389338509 : ℕ)^33*25000000000000^25 ≤ 5993654950993^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3389338509 10000000000 5993654950993 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224608109/1250000000 : ℝ)^33 ≤ (1037433702119/10000000000000 : ℝ)^25 := by
    have hnat : (224608109 : ℕ)^33*10000000000000^25 ≤ 1037433702119^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224608109 1250000000 1037433702119 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3635102779/5000000000 : ℝ)^33 ≤ (16412760789681/25000000000000 : ℝ)^25 := by
    have hnat : (3635102779 : ℕ)^33*25000000000000^25 ≤ 16412760789681^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3635102779 5000000000 16412760789681 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3389338509/10000000000 : ℝ), (-224608109/1250000000 : ℝ), (-3635102779/5000000000 : ℝ)] ![(5993654950993/25000000000000 : ℝ), (1037433702119/10000000000000 : ℝ), (16412760789681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3389338509/10000000000 : ℝ)|^33 ≤ (5993654950993/25000000000000 : ℝ)^25
        have hw : |(3389338509/10000000000 : ℝ)|=(3389338509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224608109/1250000000 : ℝ)|^33 ≤ (1037433702119/10000000000000 : ℝ)^25
        have hw : |(-224608109/1250000000 : ℝ)|=(224608109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3635102779/5000000000 : ℝ)|^33 ≤ (16412760789681/25000000000000 : ℝ)^25
        have hw : |(-3635102779/5000000000 : ℝ)|=(3635102779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6029667053/10000000000 : ℝ)*x 0 + (102388731/200000000 : ℝ)*x 1 + (21722851/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6029667053/10000000000 : ℝ)^33 ≤ (51284626632177/100000000000000 : ℝ)^25 := by
    have hnat : (6029667053 : ℕ)^33*100000000000000^25 ≤ 51284626632177^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6029667053 10000000000 51284626632177 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102388731/200000000 : ℝ)^33 ≤ (41321231605811/100000000000000 : ℝ)^25 := by
    have hnat : (102388731 : ℕ)^33*100000000000000^25 ≤ 41321231605811^25*200000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102388731 200000000 41321231605811 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21722851/156250000 : ℝ)^33 ≤ (7394141757719/100000000000000 : ℝ)^25 := by
    have hnat : (21722851 : ℕ)^33*100000000000000^25 ≤ 7394141757719^25*156250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21722851 156250000 7394141757719 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6029667053/10000000000 : ℝ), (102388731/200000000 : ℝ), (21722851/156250000 : ℝ)] ![(51284626632177/100000000000000 : ℝ), (41321231605811/100000000000000 : ℝ), (7394141757719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6029667053/10000000000 : ℝ)|^33 ≤ (51284626632177/100000000000000 : ℝ)^25
        have hw : |(6029667053/10000000000 : ℝ)|=(6029667053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(102388731/200000000 : ℝ)|^33 ≤ (41321231605811/100000000000000 : ℝ)^25
        have hw : |(102388731/200000000 : ℝ)|=(102388731/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21722851/156250000 : ℝ)|^33 ≤ (7394141757719/100000000000000 : ℝ)^25
        have hw : |(21722851/156250000 : ℝ)|=(21722851/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8160279771/10000000000 : ℝ)*x 0 + (104265757/312500000 : ℝ)*x 1 + (-33733419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8160279771/10000000000 : ℝ)^33 ≤ (76462882161549/100000000000000 : ℝ)^25 := by
    have hnat : (8160279771 : ℕ)^33*100000000000000^25 ≤ 76462882161549^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8160279771 10000000000 76462882161549 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104265757/312500000 : ℝ)^33 ≤ (11741268526557/50000000000000 : ℝ)^25 := by
    have hnat : (104265757 : ℕ)^33*50000000000000^25 ≤ 11741268526557^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104265757 312500000 11741268526557 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33733419/10000000000 : ℝ)^33 ≤ (54580772251/100000000000000 : ℝ)^25 := by
    have hnat : (33733419 : ℕ)^33*100000000000000^25 ≤ 54580772251^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33733419 10000000000 54580772251 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8160279771/10000000000 : ℝ), (104265757/312500000 : ℝ), (-33733419/10000000000 : ℝ)] ![(76462882161549/100000000000000 : ℝ), (11741268526557/50000000000000 : ℝ), (54580772251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8160279771/10000000000 : ℝ)|^33 ≤ (76462882161549/100000000000000 : ℝ)^25
        have hw : |(8160279771/10000000000 : ℝ)|=(8160279771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104265757/312500000 : ℝ)|^33 ≤ (11741268526557/50000000000000 : ℝ)^25
        have hw : |(104265757/312500000 : ℝ)|=(104265757/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33733419/10000000000 : ℝ)|^33 ≤ (54580772251/100000000000000 : ℝ)^25
        have hw : |(-33733419/10000000000 : ℝ)|=(33733419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-955452041/10000000000 : ℝ)*x 0 + (7023547/12500000 : ℝ)*x 1 + (-1160863081/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955452041/10000000000 : ℝ)^33 ≤ (450687733679/10000000000000 : ℝ)^25 := by
    have hnat : (955452041 : ℕ)^33*10000000000000^25 ≤ 450687733679^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955452041 10000000000 450687733679 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7023547/12500000 : ℝ)^33 ≤ (46723283298691/100000000000000 : ℝ)^25 := by
    have hnat : (7023547 : ℕ)^33*100000000000000^25 ≤ 46723283298691^25*12500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7023547 12500000 46723283298691 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1160863081/2000000000 : ℝ)^33 ≤ (48769839359247/100000000000000 : ℝ)^25 := by
    have hnat : (1160863081 : ℕ)^33*100000000000000^25 ≤ 48769839359247^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160863081 2000000000 48769839359247 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955452041/10000000000 : ℝ), (7023547/12500000 : ℝ), (-1160863081/2000000000 : ℝ)] ![(450687733679/10000000000000 : ℝ), (46723283298691/100000000000000 : ℝ), (48769839359247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955452041/10000000000 : ℝ)|^33 ≤ (450687733679/10000000000000 : ℝ)^25
        have hw : |(-955452041/10000000000 : ℝ)|=(955452041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7023547/12500000 : ℝ)|^33 ≤ (46723283298691/100000000000000 : ℝ)^25
        have hw : |(7023547/12500000 : ℝ)|=(7023547/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1160863081/2000000000 : ℝ)|^33 ≤ (48769839359247/100000000000000 : ℝ)^25
        have hw : |(-1160863081/2000000000 : ℝ)|=(1160863081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5805239901/10000000000 : ℝ)*x 0 + (-583110143/5000000000 : ℝ)*x 1 + (-1098774053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5805239901/10000000000 : ℝ)^33 ≤ (4878009328943/10000000000000 : ℝ)^25 := by
    have hnat : (5805239901 : ℕ)^33*10000000000000^25 ≤ 4878009328943^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5805239901 10000000000 4878009328943 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (583110143/5000000000 : ℝ)^33 ≤ (1465852896539/25000000000000 : ℝ)^25 := by
    have hnat : (583110143 : ℕ)^33*25000000000000^25 ≤ 1465852896539^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583110143 5000000000 1465852896539 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098774053/2000000000 : ℝ)^33 ≤ (907129902251/2000000000000 : ℝ)^25 := by
    have hnat : (1098774053 : ℕ)^33*2000000000000^25 ≤ 907129902251^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098774053 2000000000 907129902251 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5805239901/10000000000 : ℝ), (-583110143/5000000000 : ℝ), (-1098774053/2000000000 : ℝ)] ![(4878009328943/10000000000000 : ℝ), (1465852896539/25000000000000 : ℝ), (907129902251/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5805239901/10000000000 : ℝ)|^33 ≤ (4878009328943/10000000000000 : ℝ)^25
        have hw : |(5805239901/10000000000 : ℝ)|=(5805239901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-583110143/5000000000 : ℝ)|^33 ≤ (1465852896539/25000000000000 : ℝ)^25
        have hw : |(-583110143/5000000000 : ℝ)|=(583110143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1098774053/2000000000 : ℝ)|^33 ≤ (907129902251/2000000000000 : ℝ)^25
        have hw : |(-1098774053/2000000000 : ℝ)|=(1098774053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3926758693/10000000000 : ℝ)*x 0 + (3456239637/5000000000 : ℝ)*x 1 + (838012659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3926758693/10000000000 : ℝ)^33 ≤ (29115560982877/100000000000000 : ℝ)^25 := by
    have hnat : (3926758693 : ℕ)^33*100000000000000^25 ≤ 29115560982877^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3926758693 10000000000 29115560982877 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3456239637/5000000000 : ℝ)^33 ≤ (61420970115269/100000000000000 : ℝ)^25 := by
    have hnat : (3456239637 : ℕ)^33*100000000000000^25 ≤ 61420970115269^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3456239637 5000000000 61420970115269 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (838012659/5000000000 : ℝ)^33 ≤ (9463468888781/100000000000000 : ℝ)^25 := by
    have hnat : (838012659 : ℕ)^33*100000000000000^25 ≤ 9463468888781^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838012659 5000000000 9463468888781 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3926758693/10000000000 : ℝ), (3456239637/5000000000 : ℝ), (838012659/5000000000 : ℝ)] ![(29115560982877/100000000000000 : ℝ), (61420970115269/100000000000000 : ℝ), (9463468888781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3926758693/10000000000 : ℝ)|^33 ≤ (29115560982877/100000000000000 : ℝ)^25
        have hw : |(3926758693/10000000000 : ℝ)|=(3926758693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3456239637/5000000000 : ℝ)|^33 ≤ (61420970115269/100000000000000 : ℝ)^25
        have hw : |(3456239637/5000000000 : ℝ)|=(3456239637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(838012659/5000000000 : ℝ)|^33 ≤ (9463468888781/100000000000000 : ℝ)^25
        have hw : |(838012659/5000000000 : ℝ)|=(838012659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303060_s3_s3_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8535751207/10000000000 : ℝ)*x 0 + (560537747/2000000000 : ℝ)*x 1 + (-45807821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8535751207/10000000000 : ℝ)^33 ≤ (81140766795441/100000000000000 : ℝ)^25 := by
    have hnat : (8535751207 : ℕ)^33*100000000000000^25 ≤ 81140766795441^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8535751207 10000000000 81140766795441 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560537747/2000000000 : ℝ)^33 ≤ (18655153448129/100000000000000 : ℝ)^25 := by
    have hnat : (560537747 : ℕ)^33*100000000000000^25 ≤ 18655153448129^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560537747 2000000000 18655153448129 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45807821/5000000000 : ℝ)^33 ≤ (102039874311/50000000000000 : ℝ)^25 := by
    have hnat : (45807821 : ℕ)^33*50000000000000^25 ≤ 102039874311^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45807821 5000000000 102039874311 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8535751207/10000000000 : ℝ), (560537747/2000000000 : ℝ), (-45807821/5000000000 : ℝ)] ![(81140766795441/100000000000000 : ℝ), (18655153448129/100000000000000 : ℝ), (102039874311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8535751207/10000000000 : ℝ)|^33 ≤ (81140766795441/100000000000000 : ℝ)^25
        have hw : |(8535751207/10000000000 : ℝ)|=(8535751207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560537747/2000000000 : ℝ)|^33 ≤ (18655153448129/100000000000000 : ℝ)^25
        have hw : |(560537747/2000000000 : ℝ)|=(560537747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45807821/5000000000 : ℝ)|^33 ≤ (102039874311/50000000000000 : ℝ)^25
        have hw : |(-45807821/5000000000 : ℝ)|=(45807821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303060_s3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((79447/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79447/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40181/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40181/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-70187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-70187/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3157/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3157/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1574/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1574/3125 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91389/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  have s3_pow0 : (79447/100000 : ℝ) ^ (131/32 : ℝ) ≤ (2436813505585184983/6250000000000000000 : ℝ) := by
    have hpowers : (79447/100000 : ℝ)^131 ≤ (2436813505585184983/6250000000000000000 : ℝ)^32 := by
      have hnat : (79447 : ℕ)^131*6250000000000000000^32 ≤ 2436813505585184983^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79447 100000 2436813505585184983 6250000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79447/100000 : ℝ)) (X := (2436813505585184983/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (8686813505585184983/6250000000000000000 : ℝ) ≤ (5418717798028913/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (8686813505585184983/6250000000000000000 : ℝ)^32 ≤ (5418717798028913/5000000000000000 : ℝ)^131 := by
      have hnat : (8686813505585184983 : ℕ)^32*5000000000000000^131 ≤ 5418717798028913^131*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8686813505585184983 6250000000000000000 5418717798028913 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5418717798028913/5000000000000000 : ℝ)) (X := (8686813505585184983/6250000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (5561813505585184983/3125000000000000000 : ℝ) ≤ (11512196787400827/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (5561813505585184983/3125000000000000000 : ℝ)^32 ≤ (11512196787400827/10000000000000000 : ℝ)^131 := by
      have hnat : (5561813505585184983 : ℕ)^32*10000000000000000^131 ≤ 11512196787400827^131*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5561813505585184983 3125000000000000000 11512196787400827 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11512196787400827/10000000000000000 : ℝ)) (X := (5561813505585184983/3125000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(418717798028913/3972350000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(674761191343001/7944700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (79447/100000 : ℝ)) (alpha := (418717798028913/3972350000000000 : ℝ)) (beta := (674761191343001/7944700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (79447/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(418717798028913/3972350000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(674761191343001/7944700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (40181/50000 : ℝ) ^ (131/32 : ℝ) ≤ (20430145403182380741/50000000000000000000 : ℝ) := by
    have hpowers : (40181/50000 : ℝ)^131 ≤ (20430145403182380741/50000000000000000000 : ℝ)^32 := by
      have hnat : (40181 : ℕ)^131*50000000000000000000^32 ≤ 20430145403182380741^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40181 50000 20430145403182380741 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40181/50000 : ℝ)) (X := (20430145403182380741/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (70430145403182380741/50000000000000000000 : ℝ) ≤ (2718224426551299/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (70430145403182380741/50000000000000000000 : ℝ)^32 ≤ (2718224426551299/2500000000000000 : ℝ)^131 := by
      have hnat : (70430145403182380741 : ℕ)^32*2500000000000000^131 ≤ 2718224426551299^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70430145403182380741 50000000000000000000 2718224426551299 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2718224426551299/2500000000000000 : ℝ)) (X := (70430145403182380741/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (45430145403182380741/25000000000000000000 : ℝ) ≤ (578543336396469/500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (45430145403182380741/25000000000000000000 : ℝ)^32 ≤ (578543336396469/500000000000000 : ℝ)^131 := by
      have hnat : (45430145403182380741 : ℕ)^32*500000000000000^131 ≤ 578543336396469^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45430145403182380741 25000000000000000000 578543336396469 500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (578543336396469/500000000000000 : ℝ)) (X := (45430145403182380741/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(218224426551299/2009050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(87246127715523/1004525000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (40181/50000 : ℝ)) (alpha := (218224426551299/2009050000000000 : ℝ)) (beta := (87246127715523/1004525000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (40181/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(218224426551299/2009050000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(87246127715523/1004525000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (70187/100000 : ℝ) ^ (131/32 : ℝ) ≤ (23475415235016479351/100000000000000000000 : ℝ) := by
    have hpowers : (70187/100000 : ℝ)^131 ≤ (23475415235016479351/100000000000000000000 : ℝ)^32 := by
      have hnat : (70187 : ℕ)^131*100000000000000000000^32 ≤ 23475415235016479351^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70187 100000 23475415235016479351 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70187/100000 : ℝ)) (X := (23475415235016479351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (123475415235016479351/100000000000000000000 : ℝ) ≤ (2105720880641411/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (123475415235016479351/100000000000000000000 : ℝ)^32 ≤ (2105720880641411/2000000000000000 : ℝ)^131 := by
      have hnat : (123475415235016479351 : ℕ)^32*2000000000000000^131 ≤ 2105720880641411^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123475415235016479351 100000000000000000000 2105720880641411 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2105720880641411/2000000000000000 : ℝ)) (X := (123475415235016479351/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (73475415235016479351/50000000000000000000 : ℝ) ≤ (87887256223303/80000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (73475415235016479351/50000000000000000000 : ℝ)^32 ≤ (87887256223303/80000000000000 : ℝ)^131 := by
      have hnat : (73475415235016479351 : ℕ)^32*80000000000000^131 ≤ 87887256223303^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73475415235016479351 50000000000000000000 87887256223303 80000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (87887256223303/80000000000000 : ℝ)) (X := (73475415235016479351/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(105720880641411/1403740000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(22865131235291/350935000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (70187/100000 : ℝ)) (alpha := (105720880641411/1403740000000000 : ℝ)) (beta := (22865131235291/350935000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (70187/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(105720880641411/1403740000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(22865131235291/350935000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2073461567/10000000000 : ℝ)*X 0 0+(430448237/1000000000 : ℝ)*X 0 1+(-6322651697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((2245143629/5000000000 : ℝ)*X 1 0+(-2282923171/10000000000 : ℝ)*X 1 1+(-3002867863/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((2367773257/5000000000 : ℝ)*X 2 0+(2992762829/5000000000 : ℝ)*X 2 1+(1997402209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1852422759/10000000000 : ℝ)*X 0 0+(3624701847/10000000000 : ℝ)*X 0 1+(-3523511101/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((973272791/2500000000 : ℝ)*X 1 0+(-296108967/2000000000 : ℝ)*X 1 1+(-176546453/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((207517041/500000000 : ℝ)*X 2 0+(6934900553/10000000000 : ℝ)*X 2 1+(266530367/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2897618237/5000000000 : ℝ)*X 0 0+(3016381199/5000000000 : ℝ)*X 0 1+(-5166539/5000000000 : ℝ)*X 0 2+(2897618237/5000000000 : ℝ)*X 1 0+(3016381199/5000000000 : ℝ)*X 1 1+(-5166539/5000000000 : ℝ)*X 1 2+(2897618237/5000000000 : ℝ)*X 2 0+(3016381199/5000000000 : ℝ)*X 2 1+(-5166539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1338592827/10000000000 : ℝ)*X 0 0+(1880162417/5000000000 : ℝ)*X 0 1+(-453431203/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((3389338509/10000000000 : ℝ)*X 1 0+(-224608109/1250000000 : ℝ)*X 1 1+(-3635102779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((6029667053/10000000000 : ℝ)*X 2 0+(102388731/200000000 : ℝ)*X 2 1+(21722851/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((8160279771/10000000000 : ℝ)*X 0 0+(104265757/312500000 : ℝ)*X 0 1+(-33733419/10000000000 : ℝ)*X 0 2+(8160279771/10000000000 : ℝ)*X 1 0+(104265757/312500000 : ℝ)*X 1 1+(-33733419/10000000000 : ℝ)*X 1 2+(8160279771/10000000000 : ℝ)*X 2 0+(104265757/312500000 : ℝ)*X 2 1+(-33733419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-955452041/10000000000 : ℝ)*X 0 0+(7023547/12500000 : ℝ)*X 0 1+(-1160863081/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((5805239901/10000000000 : ℝ)*X 1 0+(-583110143/5000000000 : ℝ)*X 1 1+(-1098774053/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((3926758693/10000000000 : ℝ)*X 2 0+(3456239637/5000000000 : ℝ)*X 2 1+(838012659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((8535751207/10000000000 : ℝ)*X 0 0+(560537747/2000000000 : ℝ)*X 0 1+(-45807821/5000000000 : ℝ)*X 0 2+(8535751207/10000000000 : ℝ)*X 1 0+(560537747/2000000000 : ℝ)*X 1 1+(-45807821/5000000000 : ℝ)*X 1 2+(8535751207/10000000000 : ℝ)*X 2 0+(560537747/2000000000 : ℝ)*X 2 1+(-45807821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303060_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((3157/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3157/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (30961692557498517/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (14219126711/50000000000 : ℝ)*(base7) + (16523/31250000000 : ℝ)*(base18) + (104487244029/1000000000000 : ℝ)*(base59) + (107018143013/25000000000 : ℝ)*(major_s3_0) + (107018143013/25000000000 : ℝ)*(major_s3_1) + (107018143013/25000000000 : ℝ)*(major_s3_2) + (19634233/1000000000000 : ℝ)*(sp_s3_0) + (5542217549657/1000000000000 : ℝ)*(sp_s3_7) + (5542304324039/1000000000000 : ℝ)*(sp_s3_8) + (1385582984483/250000000000 : ℝ)*(sp_s3_9) + (782557826169/250000000000 : ℝ)*(sp_s3_13) + (49227833/500000000000 : ℝ)*(sp_s3_14) + (1539339/50000000000 : ℝ)*(sp_s3_15) + (3701623/1000000000000 : ℝ)*(sp_s3_23) + (355731096307/125000000000 : ℝ)*(f.failure) + (1108467127911/200000000000 : ℝ)*(f.sum) + (619151852760026151/1762614904375000000000000000000 : ℝ)*base63 + (456420174123487/701870000000000000000000000 : ℝ)*base64 + (16570293357391/16072400000000000000000000 : ℝ)*base67 + (10171666336411/35093500000000000000000000 : ℝ)*base68 + (7960597275651647697/55761465890000000000000000000000 : ℝ)*base71 + (42726187090927/198617500000000000000000000 : ℝ)*base73 + (65239305296847/401810000000000000000000000 : ℝ)*base74 + (9840763553731/79447000000000000000000000 : ℝ)*base76 + (925348832802498391/15961299535000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (53/625000000000000 : ℝ)*base86 + (53/625000000000000 : ℝ)*base88 + (53/625000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66161/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (171644533709444461027703907/31922599070000000000000000000000 : ℝ) := by norm_num
    linear_combination (55232400157/125000000000 : ℝ)*(base7) + (118511/200000000000 : ℝ)*(base39) + (3355229505093/1000000000000 : ℝ)*(major_s3_0) + (3355229505093/1000000000000 : ℝ)*(major_s3_1) + (3355229505093/1000000000000 : ℝ)*(major_s3_2) + (3857743/1000000000000 : ℝ)*(sp_s3_0) + (7838577/1000000000000 : ℝ)*(sp_s3_2) + (1276271/20000000000 : ℝ)*(sp_s3_8) + (2105334838443/500000000000 : ℝ)*(sp_s3_14) + (263163262793/62500000000 : ℝ)*(sp_s3_15) + (4210668179661/1000000000000 : ℝ)*(sp_s3_16) + (2672429101637/1000000000000 : ℝ)*(sp_s3_20) + (2483609/1000000000000 : ℝ)*(sp_s3_21) + (2081153/500000000000 : ℝ)*(sp_s3_27) + (2230574062687/1000000000000 : ℝ)*(f.failure) + (2105338009119/500000000000 : ℝ)*(f.sum) + (4800742572743864043/282018384700000000000000000000000 : ℝ)*base63 + (31638544770071/70187000000000000000000000 : ℝ)*base64 + (1131892648734373/2009050000000000000000000000 : ℝ)*base67 + (718067643715791/1403740000000000000000000000 : ℝ)*base68 + (13417384568306361033/278807329450000000000000000000000 : ℝ)*base71 + (7255361940301823/7944700000000000000000000000 : ℝ)*base73 + (1188113845846593/2009050000000000000000000000 : ℝ)*base74 + (2189866812020381/3972350000000000000000000000 : ℝ)*base76 + (3435178609324867897/12769039628000000000000000000000 : ℝ)*base79 + (3927/5000000000000000 : ℝ)*base87 + (3927/5000000000000000 : ℝ)*base89 + (3927/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1574/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1574/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (681805610462917195521575931/70504596175000000000000000000000 : ℝ) := by norm_num
    linear_combination (97676410807/1000000000000 : ℝ)*(base7) + (10529073/1000000000000 : ℝ)*(base11) + (1906299877/12500000000 : ℝ)*(base39) + (363317/125000000000 : ℝ)*(base43) + (3558986571787/1000000000000 : ℝ)*(major_s3_0) + (3558983665251/1000000000000 : ℝ)*(major_s3_1) + (3558986571787/1000000000000 : ℝ)*(major_s3_2) + (31189339/1000000000000 : ℝ)*(sp_s3_0) + (976047/1000000000000 : ℝ)*(sp_s3_1) + (293527/1953125000 : ℝ)*(sp_s3_9) + (146636941953/31250000000 : ℝ)*(sp_s3_21) + (4692425791397/1000000000000 : ℝ)*(sp_s3_22) + (1173068393771/250000000000 : ℝ)*(sp_s3_23) + (615927308357/250000000000 : ℝ)*(sp_s3_27) + (2366032822621/1000000000000 : ℝ)*(f.failure) + (1173106691861/250000000000 : ℝ)*(f.sum) + (65326398416518322821/282018384700000000000000000000000 : ℝ)*base63 + (25599356739513/87733750000000000000000000 : ℝ)*base64 + (59504928977341/2009050000000000000000000000 : ℝ)*base67 + (36564802142751/1403740000000000000000000000 : ℝ)*base69 + (18328107673286887181/139403664725000000000000000000000 : ℝ)*base71 + (849692604963197/7944700000000000000000000000 : ℝ)*base73 + (83075980529409/2009050000000000000000000000 : ℝ)*base75 + (772611804586449/3972350000000000000000000000 : ℝ)*base76 + (56130331853717273749/319225990700000000000000000000000 : ℝ)*base78 + (2459/5000000000000000 : ℝ)*base86 + (2459/5000000000000000 : ℝ)*base88 + (2459/5000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((79447/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79447/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40181/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40181/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-70187/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-70187/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3157/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3157/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1574/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1574/3125 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c303060_s3 p hpa hpb X hX hprev2

#print axioms solution

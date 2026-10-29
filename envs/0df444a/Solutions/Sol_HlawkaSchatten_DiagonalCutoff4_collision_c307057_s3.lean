-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307057_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:13:41.299208+00:00
-- url     : https://prove2.me/submissions/3ea9f428-fd74-4b88-a28e-4c1c44bccb74

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
theorem collision_support_c307057_s3_s3_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (854703501/2500000000 : ℝ)*x 0 + (-106828123/312500000 : ℝ)*x 1 + (2981388267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854703501/2500000000 : ℝ)^17 ≤ (2457268102829/10000000000000 : ℝ)^13 := by
    have hnat : (854703501 : ℕ)^17*10000000000000^13 ≤ 2457268102829^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854703501 2500000000 2457268102829 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106828123/312500000 : ℝ)^17 ≤ (307121614227/1250000000000 : ℝ)^13 := by
    have hnat : (106828123 : ℕ)^17*1250000000000^13 ≤ 307121614227^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106828123 312500000 307121614227 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2981388267/5000000000 : ℝ)^17 ≤ (12714397455457/25000000000000 : ℝ)^13 := by
    have hnat : (2981388267 : ℕ)^17*25000000000000^13 ≤ 12714397455457^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981388267 5000000000 12714397455457 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854703501/2500000000 : ℝ), (-106828123/312500000 : ℝ), (2981388267/5000000000 : ℝ)] ![(2457268102829/10000000000000 : ℝ), (307121614227/1250000000000 : ℝ), (12714397455457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854703501/2500000000 : ℝ)|^17 ≤ (2457268102829/10000000000000 : ℝ)^13
        have hw : |(854703501/2500000000 : ℝ)|=(854703501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106828123/312500000 : ℝ)|^17 ≤ (307121614227/1250000000000 : ℝ)^13
        have hw : |(-106828123/312500000 : ℝ)|=(106828123/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2981388267/5000000000 : ℝ)|^17 ≤ (12714397455457/25000000000000 : ℝ)^13
        have hw : |(2981388267/5000000000 : ℝ)|=(2981388267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4555495919/10000000000 : ℝ)*x 0 + (4555861133/10000000000 : ℝ)*x 1 + (478201673/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4555495919/10000000000 : ℝ)^17 ≤ (3576594560689/10000000000000 : ℝ)^13 := by
    have hnat : (4555495919 : ℕ)^17*10000000000000^13 ≤ 3576594560689^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555495919 10000000000 3576594560689 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4555861133/10000000000 : ℝ)^17 ≤ (3576969527123/10000000000000 : ℝ)^13 := by
    have hnat : (4555861133 : ℕ)^17*10000000000000^13 ≤ 3576969527123^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555861133 10000000000 3576969527123 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478201673/1250000000 : ℝ)^17 ≤ (28464359111151/100000000000000 : ℝ)^13 := by
    have hnat : (478201673 : ℕ)^17*100000000000000^13 ≤ 28464359111151^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478201673 1250000000 28464359111151 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4555495919/10000000000 : ℝ), (4555861133/10000000000 : ℝ), (478201673/1250000000 : ℝ)] ![(3576594560689/10000000000000 : ℝ), (3576969527123/10000000000000 : ℝ), (28464359111151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4555495919/10000000000 : ℝ)|^17 ≤ (3576594560689/10000000000000 : ℝ)^13
        have hw : |(4555495919/10000000000 : ℝ)|=(4555495919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4555861133/10000000000 : ℝ)|^17 ≤ (3576969527123/10000000000000 : ℝ)^13
        have hw : |(4555861133/10000000000 : ℝ)|=(4555861133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(478201673/1250000000 : ℝ)|^17 ≤ (28464359111151/100000000000000 : ℝ)^13
        have hw : |(478201673/1250000000 : ℝ)|=(478201673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3228598423/10000000000 : ℝ)*x 0 + (287431231/1000000000 : ℝ)*x 1 + (6559590583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3228598423/10000000000 : ℝ)^17 ≤ (1425021581291/6250000000000 : ℝ)^13 := by
    have hnat : (3228598423 : ℕ)^17*6250000000000^13 ≤ 1425021581291^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3228598423 10000000000 1425021581291 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287431231/1000000000 : ℝ)^17 ≤ (9792622707859/50000000000000 : ℝ)^13 := by
    have hnat : (287431231 : ℕ)^17*50000000000000^13 ≤ 9792622707859^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287431231 1000000000 9792622707859 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6559590583/10000000000 : ℝ)^17 ≤ (28807204633461/50000000000000 : ℝ)^13 := by
    have hnat : (6559590583 : ℕ)^17*50000000000000^13 ≤ 28807204633461^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6559590583 10000000000 28807204633461 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3228598423/10000000000 : ℝ), (287431231/1000000000 : ℝ), (6559590583/10000000000 : ℝ)] ![(1425021581291/6250000000000 : ℝ), (9792622707859/50000000000000 : ℝ), (28807204633461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3228598423/10000000000 : ℝ)|^17 ≤ (1425021581291/6250000000000 : ℝ)^13
        have hw : |(-3228598423/10000000000 : ℝ)|=(3228598423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(287431231/1000000000 : ℝ)|^17 ≤ (9792622707859/50000000000000 : ℝ)^13
        have hw : |(287431231/1000000000 : ℝ)|=(287431231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6559590583/10000000000 : ℝ)|^17 ≤ (28807204633461/50000000000000 : ℝ)^13
        have hw : |(6559590583/10000000000 : ℝ)|=(6559590583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1614144771/5000000000 : ℝ)*x 0 + (-2874037323/10000000000 : ℝ)*x 1 + (1640013063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1614144771/5000000000 : ℝ)^17 ≤ (1424843303279/6250000000000 : ℝ)^13 := by
    have hnat : (1614144771 : ℕ)^17*6250000000000^13 ≤ 1424843303279^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614144771 5000000000 1424843303279 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2874037323/10000000000 : ℝ)^17 ≤ (9791397594129/50000000000000 : ℝ)^13 := by
    have hnat : (2874037323 : ℕ)^17*50000000000000^13 ≤ 9791397594129^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2874037323 10000000000 9791397594129 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1640013063/2500000000 : ℝ)^17 ≤ (57619711946251/100000000000000 : ℝ)^13 := by
    have hnat : (1640013063 : ℕ)^17*100000000000000^13 ≤ 57619711946251^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640013063 2500000000 57619711946251 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1614144771/5000000000 : ℝ), (-2874037323/10000000000 : ℝ), (1640013063/2500000000 : ℝ)] ![(1424843303279/6250000000000 : ℝ), (9791397594129/50000000000000 : ℝ), (57619711946251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1614144771/5000000000 : ℝ)|^17 ≤ (1424843303279/6250000000000 : ℝ)^13
        have hw : |(1614144771/5000000000 : ℝ)|=(1614144771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2874037323/10000000000 : ℝ)|^17 ≤ (9791397594129/50000000000000 : ℝ)^13
        have hw : |(-2874037323/10000000000 : ℝ)|=(2874037323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1640013063/2500000000 : ℝ)|^17 ≤ (57619711946251/100000000000000 : ℝ)^13
        have hw : |(1640013063/2500000000 : ℝ)|=(1640013063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5271866757/10000000000 : ℝ)*x 0 + (6360677857/10000000000 : ℝ)*x 1 + (-93820883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271866757/10000000000 : ℝ)^17 ≤ (43292734455743/100000000000000 : ℝ)^13 := by
    have hnat : (5271866757 : ℕ)^17*100000000000000^13 ≤ 43292734455743^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271866757 10000000000 43292734455743 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6360677857/10000000000 : ℝ)^17 ≤ (2767023917761/5000000000000 : ℝ)^13 := by
    have hnat : (6360677857 : ℕ)^17*5000000000000^13 ≤ 2767023917761^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6360677857 10000000000 2767023917761 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93820883/2500000000 : ℝ)^17 ≤ (341696793117/25000000000000 : ℝ)^13 := by
    have hnat : (93820883 : ℕ)^17*25000000000000^13 ≤ 341696793117^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93820883 2500000000 341696793117 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271866757/10000000000 : ℝ), (6360677857/10000000000 : ℝ), (-93820883/2500000000 : ℝ)] ![(43292734455743/100000000000000 : ℝ), (2767023917761/5000000000000 : ℝ), (341696793117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271866757/10000000000 : ℝ)|^17 ≤ (43292734455743/100000000000000 : ℝ)^13
        have hw : |(5271866757/10000000000 : ℝ)|=(5271866757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6360677857/10000000000 : ℝ)|^17 ≤ (2767023917761/5000000000000 : ℝ)^13
        have hw : |(6360677857/10000000000 : ℝ)|=(6360677857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93820883/2500000000 : ℝ)|^17 ≤ (341696793117/25000000000000 : ℝ)^13
        have hw : |(-93820883/2500000000 : ℝ)|=(93820883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_12 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4601738411/10000000000 : ℝ)*x 0 + (5552146321/10000000000 : ℝ)*x 1 + (2629338679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4601738411/10000000000 : ℝ)^17 ≤ (9060363166797/25000000000000 : ℝ)^13 := by
    have hnat : (4601738411 : ℕ)^17*25000000000000^13 ≤ 9060363166797^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601738411 10000000000 9060363166797 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5552146321/10000000000 : ℝ)^17 ≤ (11581731626353/25000000000000 : ℝ)^13 := by
    have hnat : (5552146321 : ℕ)^17*25000000000000^13 ≤ 11581731626353^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5552146321 10000000000 11581731626353 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629338679/10000000000 : ℝ)^17 ≤ (8715810406809/50000000000000 : ℝ)^13 := by
    have hnat : (2629338679 : ℕ)^17*50000000000000^13 ≤ 8715810406809^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629338679 10000000000 8715810406809 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4601738411/10000000000 : ℝ), (5552146321/10000000000 : ℝ), (2629338679/10000000000 : ℝ)] ![(9060363166797/25000000000000 : ℝ), (11581731626353/25000000000000 : ℝ), (8715810406809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4601738411/10000000000 : ℝ)|^17 ≤ (9060363166797/25000000000000 : ℝ)^13
        have hw : |(4601738411/10000000000 : ℝ)|=(4601738411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5552146321/10000000000 : ℝ)|^17 ≤ (11581731626353/25000000000000 : ℝ)^13
        have hw : |(5552146321/10000000000 : ℝ)|=(5552146321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629338679/10000000000 : ℝ)|^17 ≤ (8715810406809/50000000000000 : ℝ)^13
        have hw : |(2629338679/10000000000 : ℝ)|=(2629338679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2874623253/10000000000 : ℝ)*x 0 + (129131893/400000000 : ℝ)*x 1 + (6559591443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2874623253/10000000000 : ℝ)^17 ≤ (4897004027557/25000000000000 : ℝ)^13 := by
    have hnat : (2874623253 : ℕ)^17*25000000000000^13 ≤ 4897004027557^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2874623253 10000000000 4897004027557 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129131893/400000000 : ℝ)^17 ≤ (712423897679/3125000000000 : ℝ)^13 := by
    have hnat : (129131893 : ℕ)^17*3125000000000^13 ≤ 712423897679^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129131893 400000000 712423897679 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6559591443/10000000000 : ℝ)^17 ≤ (1440360478617/2500000000000 : ℝ)^13 := by
    have hnat : (6559591443 : ℕ)^17*2500000000000^13 ≤ 1440360478617^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6559591443 10000000000 1440360478617 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2874623253/10000000000 : ℝ), (129131893/400000000 : ℝ), (6559591443/10000000000 : ℝ)] ![(4897004027557/25000000000000 : ℝ), (712423897679/3125000000000 : ℝ), (1440360478617/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2874623253/10000000000 : ℝ)|^17 ≤ (4897004027557/25000000000000 : ℝ)^13
        have hw : |(-2874623253/10000000000 : ℝ)|=(2874623253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129131893/400000000 : ℝ)|^17 ≤ (712423897679/3125000000000 : ℝ)^13
        have hw : |(129131893/400000000 : ℝ)|=(129131893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6559591443/10000000000 : ℝ)|^17 ≤ (1440360478617/2500000000000 : ℝ)^13
        have hw : |(6559591443/10000000000 : ℝ)|=(6559591443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (287434841/1000000000 : ℝ)*x 0 + (-3227988667/10000000000 : ℝ)*x 1 + (3280026411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287434841/1000000000 : ℝ)^17 ≤ (19585567084321/100000000000000 : ℝ)^13 := by
    have hnat : (287434841 : ℕ)^17*100000000000000^13 ≤ 19585567084321^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287434841 1000000000 19585567084321 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3227988667/10000000000 : ℝ)^17 ≤ (22794714418661/100000000000000 : ℝ)^13 := by
    have hnat : (3227988667 : ℕ)^17*100000000000000^13 ≤ 22794714418661^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3227988667 10000000000 22794714418661 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3280026411/5000000000 : ℝ)^17 ≤ (57619718493279/100000000000000 : ℝ)^13 := by
    have hnat : (3280026411 : ℕ)^17*100000000000000^13 ≤ 57619718493279^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3280026411 5000000000 57619718493279 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(287434841/1000000000 : ℝ), (-3227988667/10000000000 : ℝ), (3280026411/5000000000 : ℝ)] ![(19585567084321/100000000000000 : ℝ), (22794714418661/100000000000000 : ℝ), (57619718493279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(287434841/1000000000 : ℝ)|^17 ≤ (19585567084321/100000000000000 : ℝ)^13
        have hw : |(287434841/1000000000 : ℝ)|=(287434841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3227988667/10000000000 : ℝ)|^17 ≤ (22794714418661/100000000000000 : ℝ)^13
        have hw : |(-3227988667/10000000000 : ℝ)|=(3227988667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3280026411/5000000000 : ℝ)|^17 ≤ (57619718493279/100000000000000 : ℝ)^13
        have hw : |(3280026411/5000000000 : ℝ)|=(3280026411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3180118839/5000000000 : ℝ)*x 0 + (5272333279/10000000000 : ℝ)*x 1 + (-187641567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3180118839/5000000000 : ℝ)^17 ≤ (27667735146173/50000000000000 : ℝ)^13 := by
    have hnat : (3180118839 : ℕ)^17*50000000000000^13 ≤ 27667735146173^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3180118839 5000000000 27667735146173 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272333279/10000000000 : ℝ)^17 ≤ (43297744415099/100000000000000 : ℝ)^13 := by
    have hnat : (5272333279 : ℕ)^17*100000000000000^13 ≤ 43297744415099^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272333279 10000000000 43297744415099 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187641567/5000000000 : ℝ)^17 ≤ (1366785276941/100000000000000 : ℝ)^13 := by
    have hnat : (187641567 : ℕ)^17*100000000000000^13 ≤ 1366785276941^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187641567 5000000000 1366785276941 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3180118839/5000000000 : ℝ), (5272333279/10000000000 : ℝ), (-187641567/5000000000 : ℝ)] ![(27667735146173/50000000000000 : ℝ), (43297744415099/100000000000000 : ℝ), (1366785276941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3180118839/5000000000 : ℝ)|^17 ≤ (27667735146173/50000000000000 : ℝ)^13
        have hw : |(3180118839/5000000000 : ℝ)|=(3180118839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272333279/10000000000 : ℝ)|^17 ≤ (43297744415099/100000000000000 : ℝ)^13
        have hw : |(5272333279/10000000000 : ℝ)|=(5272333279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187641567/5000000000 : ℝ)|^17 ≤ (1366785276941/100000000000000 : ℝ)^13
        have hw : |(-187641567/5000000000 : ℝ)|=(187641567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_18 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2775881237/5000000000 : ℝ)*x 0 + (4602145947/10000000000 : ℝ)*x 1 + (657334411/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2775881237/5000000000 : ℝ)^17 ≤ (46322738264199/100000000000000 : ℝ)^13 := by
    have hnat : (2775881237 : ℕ)^17*100000000000000^13 ≤ 46322738264199^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775881237 5000000000 46322738264199 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4602145947/10000000000 : ℝ)^17 ≤ (18122824940699/50000000000000 : ℝ)^13 := by
    have hnat : (4602145947 : ℕ)^17*50000000000000^13 ≤ 18122824940699^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4602145947 10000000000 18122824940699 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657334411/2500000000 : ℝ)^17 ≤ (17431611840629/100000000000000 : ℝ)^13 := by
    have hnat : (657334411 : ℕ)^17*100000000000000^13 ≤ 17431611840629^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657334411 2500000000 17431611840629 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2775881237/5000000000 : ℝ), (4602145947/10000000000 : ℝ), (657334411/2500000000 : ℝ)] ![(46322738264199/100000000000000 : ℝ), (18122824940699/50000000000000 : ℝ), (17431611840629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2775881237/5000000000 : ℝ)|^17 ≤ (46322738264199/100000000000000 : ℝ)^13
        have hw : |(2775881237/5000000000 : ℝ)|=(2775881237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4602145947/10000000000 : ℝ)|^17 ≤ (18122824940699/50000000000000 : ℝ)^13
        have hw : |(4602145947/10000000000 : ℝ)|=(4602145947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657334411/2500000000 : ℝ)|^17 ≤ (17431611840629/100000000000000 : ℝ)^13
        have hw : |(657334411/2500000000 : ℝ)|=(657334411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_19 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1880052043/5000000000 : ℝ)*x 0 + (97256091/312500000 : ℝ)*x 1 + (5925297321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1880052043/5000000000 : ℝ)^17 ≤ (13914324845453/50000000000000 : ℝ)^13 := by
    have hnat : (1880052043 : ℕ)^17*50000000000000^13 ≤ 13914324845453^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880052043 5000000000 13914324845453 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97256091/312500000 : ℝ)^17 ≤ (21731381630857/100000000000000 : ℝ)^13 := by
    have hnat : (97256091 : ℕ)^17*100000000000000^13 ≤ 21731381630857^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97256091 312500000 21731381630857 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5925297321/10000000000 : ℝ)^17 ≤ (25219984331707/50000000000000 : ℝ)^13 := by
    have hnat : (5925297321 : ℕ)^17*50000000000000^13 ≤ 25219984331707^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5925297321 10000000000 25219984331707 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1880052043/5000000000 : ℝ), (97256091/312500000 : ℝ), (5925297321/10000000000 : ℝ)] ![(13914324845453/50000000000000 : ℝ), (21731381630857/100000000000000 : ℝ), (25219984331707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1880052043/5000000000 : ℝ)|^17 ≤ (13914324845453/50000000000000 : ℝ)^13
        have hw : |(-1880052043/5000000000 : ℝ)|=(1880052043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97256091/312500000 : ℝ)|^17 ≤ (21731381630857/100000000000000 : ℝ)^13
        have hw : |(97256091/312500000 : ℝ)|=(97256091/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5925297321/10000000000 : ℝ)|^17 ≤ (25219984331707/50000000000000 : ℝ)^13
        have hw : |(5925297321/10000000000 : ℝ)|=(5925297321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (778061597/2500000000 : ℝ)*x 0 + (-1879762457/5000000000 : ℝ)*x 1 + (5925758621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (778061597/2500000000 : ℝ)^17 ≤ (10865925833913/50000000000000 : ℝ)^13 := by
    have hnat : (778061597 : ℕ)^17*50000000000000^13 ≤ 10865925833913^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778061597 2500000000 10865925833913 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1879762457/5000000000 : ℝ)^17 ≤ (27823044439431/100000000000000 : ℝ)^13 := by
    have hnat : (1879762457 : ℕ)^17*100000000000000^13 ≤ 27823044439431^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879762457 5000000000 27823044439431 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5925758621/10000000000 : ℝ)^17 ≤ (2017804155257/4000000000000 : ℝ)^13 := by
    have hnat : (5925758621 : ℕ)^17*4000000000000^13 ≤ 2017804155257^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5925758621 10000000000 2017804155257 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(778061597/2500000000 : ℝ), (-1879762457/5000000000 : ℝ), (5925758621/10000000000 : ℝ)] ![(10865925833913/50000000000000 : ℝ), (27823044439431/100000000000000 : ℝ), (2017804155257/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(778061597/2500000000 : ℝ)|^17 ≤ (10865925833913/50000000000000 : ℝ)^13
        have hw : |(778061597/2500000000 : ℝ)|=(778061597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1879762457/5000000000 : ℝ)|^17 ≤ (27823044439431/100000000000000 : ℝ)^13
        have hw : |(-1879762457/5000000000 : ℝ)|=(1879762457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5925758621/10000000000 : ℝ)|^17 ≤ (2017804155257/4000000000000 : ℝ)^13
        have hw : |(5925758621/10000000000 : ℝ)|=(5925758621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5880652299/10000000000 : ℝ)*x 0 + (5501687949/10000000000 : ℝ)*x 1 + (-898262857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5880652299/10000000000 : ℝ)^17 ≤ (12485890193243/25000000000000 : ℝ)^13 := by
    have hnat : (5880652299 : ℕ)^17*25000000000000^13 ≤ 12485890193243^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5880652299 10000000000 12485890193243 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501687949/10000000000 : ℝ)^17 ≤ (45777129376439/100000000000000 : ℝ)^13 := by
    have hnat : (5501687949 : ℕ)^17*100000000000000^13 ≤ 45777129376439^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501687949 10000000000 45777129376439 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898262857/10000000000 : ℝ)^17 ≤ (4279309835613/100000000000000 : ℝ)^13 := by
    have hnat : (898262857 : ℕ)^17*100000000000000^13 ≤ 4279309835613^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898262857 10000000000 4279309835613 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5880652299/10000000000 : ℝ), (5501687949/10000000000 : ℝ), (-898262857/10000000000 : ℝ)] ![(12485890193243/25000000000000 : ℝ), (45777129376439/100000000000000 : ℝ), (4279309835613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5880652299/10000000000 : ℝ)|^17 ≤ (12485890193243/25000000000000 : ℝ)^13
        have hw : |(5880652299/10000000000 : ℝ)|=(5880652299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501687949/10000000000 : ℝ)|^17 ≤ (45777129376439/100000000000000 : ℝ)^13
        have hw : |(5501687949/10000000000 : ℝ)|=(5501687949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-898262857/10000000000 : ℝ)|^17 ≤ (4279309835613/100000000000000 : ℝ)^13
        have hw : |(-898262857/10000000000 : ℝ)|=(898262857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s3_s3_25 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (65531669/156250000 : ℝ)*x 0 + (2497289407/5000000000 : ℝ)*x 1 + (3732280741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65531669/156250000 : ℝ)^17 ≤ (32100938304663/100000000000000 : ℝ)^13 := by
    have hnat : (65531669 : ℕ)^17*100000000000000^13 ≤ 32100938304663^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65531669 156250000 32100938304663 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2497289407/5000000000 : ℝ)^17 ≤ (1613575472661/4000000000000 : ℝ)^13 := by
    have hnat : (2497289407 : ℕ)^17*4000000000000^13 ≤ 1613575472661^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497289407 5000000000 1613575472661 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3732280741/10000000000 : ℝ)^17 ≤ (13779837429423/50000000000000 : ℝ)^13 := by
    have hnat : (3732280741 : ℕ)^17*50000000000000^13 ≤ 13779837429423^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732280741 10000000000 13779837429423 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65531669/156250000 : ℝ), (2497289407/5000000000 : ℝ), (3732280741/10000000000 : ℝ)] ![(32100938304663/100000000000000 : ℝ), (1613575472661/4000000000000 : ℝ), (13779837429423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65531669/156250000 : ℝ)|^17 ≤ (32100938304663/100000000000000 : ℝ)^13
        have hw : |(65531669/156250000 : ℝ)|=(65531669/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2497289407/5000000000 : ℝ)|^17 ≤ (1613575472661/4000000000000 : ℝ)^13
        have hw : |(2497289407/5000000000 : ℝ)|=(2497289407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3732280741/10000000000 : ℝ)|^17 ≤ (13779837429423/50000000000000 : ℝ)^13
        have hw : |(3732280741/10000000000 : ℝ)|=(3732280741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307057_s3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((69361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69331/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3021/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3021/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4623/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4623/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36981/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36981/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4913/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4913/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s3_pow0 : (69361/100000 : ℝ) ^ (135/32 : ℝ) ≤ (5341280356523958787/25000000000000000000 : ℝ) := by
    have hpowers : (69361/100000 : ℝ)^135 ≤ (5341280356523958787/25000000000000000000 : ℝ)^32 := by
      have hnat : (69361 : ℕ)^135*25000000000000000000^32 ≤ 5341280356523958787^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69361 100000 5341280356523958787 25000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69361/100000 : ℝ)) (X := (5341280356523958787/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (30341280356523958787/25000000000000000000 : ℝ) ≤ (2617419757312573/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (30341280356523958787/25000000000000000000 : ℝ)^32 ≤ (2617419757312573/2500000000000000 : ℝ)^135 := by
      have hnat : (30341280356523958787 : ℕ)^32*2500000000000000^135 ≤ 2617419757312573^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30341280356523958787 25000000000000000000 2617419757312573 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2617419757312573/2500000000000000 : ℝ)) (X := (30341280356523958787/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (17841280356523958787/12500000000000000000 : ℝ) ≤ (5439963932261171/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (17841280356523958787/12500000000000000000 : ℝ)^32 ≤ (5439963932261171/5000000000000000 : ℝ)^135 := by
      have hnat : (17841280356523958787 : ℕ)^32*5000000000000000^135 ≤ 5439963932261171^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17841280356523958787 12500000000000000000 5439963932261171 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5439963932261171/5000000000000000 : ℝ)) (X := (17841280356523958787/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(117419757312573/1734025000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(8204976705441/138722000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (69361/100000 : ℝ)) (alpha := (117419757312573/1734025000000000 : ℝ)) (beta := (8204976705441/138722000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (69361/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(117419757312573/1734025000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(8204976705441/138722000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (69331/100000 : ℝ) ^ (135/32 : ℝ) ≤ (21326163776282543659/100000000000000000000 : ℝ) := by
    have hpowers : (69331/100000 : ℝ)^135 ≤ (21326163776282543659/100000000000000000000 : ℝ)^32 := by
      have hnat : (69331 : ℕ)^135*100000000000000000000^32 ≤ 21326163776282543659^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69331 100000 21326163776282543659 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69331/100000 : ℝ)) (X := (21326163776282543659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (121326163776282543659/100000000000000000000 : ℝ) ≤ (2617220579192669/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (121326163776282543659/100000000000000000000 : ℝ)^32 ≤ (2617220579192669/2500000000000000 : ℝ)^135 := by
      have hnat : (121326163776282543659 : ℕ)^32*2500000000000000^135 ≤ 2617220579192669^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121326163776282543659 100000000000000000000 2617220579192669 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2617220579192669/2500000000000000 : ℝ)) (X := (121326163776282543659/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (71326163776282543659/50000000000000000000 : ℝ) ≤ (10878519745301809/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (71326163776282543659/50000000000000000000 : ℝ)^32 ≤ (10878519745301809/10000000000000000 : ℝ)^135 := by
      have hnat : (71326163776282543659 : ℕ)^32*10000000000000000^135 ≤ 10878519745301809^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71326163776282543659 50000000000000000000 10878519745301809 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10878519745301809/10000000000000000 : ℝ)) (X := (71326163776282543659/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(117220579192669/1733275000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(409637428531133/6933100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (69331/100000 : ℝ)) (alpha := (117220579192669/1733275000000000 : ℝ)) (beta := (409637428531133/6933100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (69331/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(117220579192669/1733275000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(409637428531133/6933100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (3021/20000 : ℝ) ^ (135/32 : ℝ) ≤ (2151768746980259/6250000000000000000 : ℝ) := by
    have hpowers : (3021/20000 : ℝ)^135 ≤ (2151768746980259/6250000000000000000 : ℝ)^32 := by
      have hnat : (3021 : ℕ)^135*6250000000000000000^32 ≤ 2151768746980259^32*20000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3021 20000 2151768746980259 6250000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3021/20000 : ℝ)) (X := (2151768746980259/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (6252151768746980259/6250000000000000000 : ℝ) ≤ (10000815971061011/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (6252151768746980259/6250000000000000000 : ℝ)^32 ≤ (10000815971061011/10000000000000000 : ℝ)^135 := by
      have hnat : (6252151768746980259 : ℕ)^32*10000000000000000^135 ≤ 10000815971061011^135*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252151768746980259 6250000000000000000 10000815971061011 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000815971061011/10000000000000000 : ℝ)) (X := (6252151768746980259/6250000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (3127151768746980259/3125000000000000000 : ℝ) ≤ (10001631727888569/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (3127151768746980259/3125000000000000000 : ℝ)^32 ≤ (10001631727888569/10000000000000000 : ℝ)^135 := by
      have hnat : (3127151768746980259 : ℕ)^32*10000000000000000^135 ≤ 10001631727888569^135*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127151768746980259 3125000000000000000 10001631727888569 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001631727888569/10000000000000000 : ℝ)) (X := (3127151768746980259/3125000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(815971061011/1510500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(407878413779/755250000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (3021/20000 : ℝ)) (alpha := (815971061011/1510500000000000 : ℝ)) (beta := (407878413779/755250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (3021/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(815971061011/1510500000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(407878413779/755250000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_1 : ((854703501/2500000000 : ℝ)*X 1 0+(-106828123/312500000 : ℝ)*X 1 1+(2981388267/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((4555495919/10000000000 : ℝ)*X 0 0+(4555861133/10000000000 : ℝ)*X 0 1+(478201673/1250000000 : ℝ)*X 0 2+(4555495919/10000000000 : ℝ)*X 1 0+(4555861133/10000000000 : ℝ)*X 1 1+(478201673/1250000000 : ℝ)*X 1 2+(4555495919/10000000000 : ℝ)*X 2 0+(4555861133/10000000000 : ℝ)*X 2 1+(478201673/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-3228598423/10000000000 : ℝ)*X 0 0+(287431231/1000000000 : ℝ)*X 0 1+(6559590583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((1614144771/5000000000 : ℝ)*X 1 0+(-2874037323/10000000000 : ℝ)*X 1 1+(1640013063/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((5271866757/10000000000 : ℝ)*X 2 0+(6360677857/10000000000 : ℝ)*X 2 1+(-93820883/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_12 : ((4601738411/10000000000 : ℝ)*X 0 0+(5552146321/10000000000 : ℝ)*X 0 1+(2629338679/10000000000 : ℝ)*X 0 2+(4601738411/10000000000 : ℝ)*X 1 0+(5552146321/10000000000 : ℝ)*X 1 1+(2629338679/10000000000 : ℝ)*X 1 2+(4601738411/10000000000 : ℝ)*X 2 0+(5552146321/10000000000 : ℝ)*X 2 1+(2629338679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((-2874623253/10000000000 : ℝ)*X 0 0+(129131893/400000000 : ℝ)*X 0 1+(6559591443/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((287434841/1000000000 : ℝ)*X 1 0+(-3227988667/10000000000 : ℝ)*X 1 1+(3280026411/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((3180118839/5000000000 : ℝ)*X 2 0+(5272333279/10000000000 : ℝ)*X 2 1+(-187641567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_18 : ((2775881237/5000000000 : ℝ)*X 0 0+(4602145947/10000000000 : ℝ)*X 0 1+(657334411/2500000000 : ℝ)*X 0 2+(2775881237/5000000000 : ℝ)*X 1 0+(4602145947/10000000000 : ℝ)*X 1 1+(657334411/2500000000 : ℝ)*X 1 2+(2775881237/5000000000 : ℝ)*X 2 0+(4602145947/10000000000 : ℝ)*X 2 1+(657334411/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_19 : ((-1880052043/5000000000 : ℝ)*X 0 0+(97256091/312500000 : ℝ)*X 0 1+(5925297321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((778061597/2500000000 : ℝ)*X 1 0+(-1879762457/5000000000 : ℝ)*X 1 1+(5925758621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((5880652299/10000000000 : ℝ)*X 2 0+(5501687949/10000000000 : ℝ)*X 2 1+(-898262857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_25 : ((65531669/156250000 : ℝ)*X 0 0+(2497289407/5000000000 : ℝ)*X 0 1+(3732280741/10000000000 : ℝ)*X 0 2+(65531669/156250000 : ℝ)*X 1 0+(2497289407/5000000000 : ℝ)*X 1 1+(3732280741/10000000000 : ℝ)*X 1 2+(65531669/156250000 : ℝ)*X 2 0+(2497289407/5000000000 : ℝ)*X 2 1+(3732280741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s3_s3_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((4623/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4623/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (72385775960383314456962611497/12743498851150000000000000000000000 : ℝ) := by norm_num
    linear_combination (166479/50000000000 : ℝ)*(base23) + (476167/250000000000 : ℝ)*(base39) + (1634547/1000000000000 : ℝ)*(base49) + (1513752613287/500000000000 : ℝ)*(base59) + (274372455817/200000000000 : ℝ)*(base60) + (1312274108319/200000000000 : ℝ)*(major_s3_0) + (1312274108319/200000000000 : ℝ)*(major_s3_1) + (1312274108319/200000000000 : ℝ)*(major_s3_2) + (4450865321361/500000000000 : ℝ)*(sp_s3_7) + (2225449197503/250000000000 : ℝ)*(sp_s3_8) + (556362091277/62500000000 : ℝ)*(sp_s3_9) + (4220912704081/1000000000000 : ℝ)*(sp_s3_12) + (6614729/100000000000 : ℝ)*(sp_s3_13) + (29695689/1000000000000 : ℝ)*(sp_s3_25) + (422094239977/100000000000 : ℝ)*(f.failure) + (2225449197503/250000000000 : ℝ)*(f.sum) + (56093133085829557/367454300000000000000000000000 : ℝ)*base62 + (2548511024369/25175000000000000000000000 : ℝ)*base65 + (244759782498499/1386620000000000000000000000 : ℝ)*base67 + (19981842494833/100700000000000000000000000 : ℝ)*base68 + (196630883303917109/1746163175000000000000000000000 : ℝ)*base71 + (159800722823517/693610000000000000000000000 : ℝ)*base72 + (20096714652587/693310000000000000000000000 : ℝ)*base74 + (190895880561943/693610000000000000000000000 : ℝ)*base77 + (4747612058787053371/96177349820000000000000000000000 : ℝ)*base78 + (663/1250000000000000 : ℝ)*base86 + (663/1250000000000000 : ℝ)*base88 + (663/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36981/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36981/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (264384461075760844335889624649/63717494255750000000000000000000000 : ℝ) := by norm_num
    linear_combination (2265293/500000000000 : ℝ)*(base21) + (3027455967341/1000000000000 : ℝ)*(base59) + (1655757673139/1000000000000 : ℝ)*(base60) + (3280657708949/500000000000 : ℝ)*(major_s3_0) + (3280657708949/500000000000 : ℝ)*(major_s3_1) + (3280657708949/500000000000 : ℝ)*(major_s3_2) + (200841/1000000000000 : ℝ)*(sp_s3_1) + (1633911/200000000000 : ℝ)*(sp_s3_6) + (9376697/200000000000 : ℝ)*(sp_s3_8) + (890172251409/100000000000 : ℝ)*(sp_s3_13) + (2225418857441/250000000000 : ℝ)*(sp_s3_14) + (2225423833123/250000000000 : ℝ)*(sp_s3_15) + (844179753807/200000000000 : ℝ)*(sp_s3_18) + (22651013/1000000000000 : ℝ)*(sp_s3_21) + (4220906938589/1000000000000 : ℝ)*(f.failure) + (890172251409/100000000000 : ℝ)*(f.sum) + (6141607084722017/86122101562500000000000000000 : ℝ)*base63 + (133301669928349/94406250000000000000000000 : ℝ)*base64 + (1830706485912933/3466550000000000000000000000 : ℝ)*base66 + (20515087568083/94406250000000000000000000 : ℝ)*base68 + (60656325699451731347/52384895250000000000000000000000 : ℝ)*base70 + (91924011532853/173402500000000000000000000 : ℝ)*base72 + (2462517509573833/1733275000000000000000000000 : ℝ)*base74 + (3226784312181717/3468050000000000000000000000 : ℝ)*base76 + (27231581237889038309/120221687275000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (2141/12500000000000000 : ℝ)*base86 + (2141/12500000000000000 : ℝ)*base88 + (2141/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4913/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4913/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (55477597650046506604400609/8730815875000000000000000000000 : ℝ) := by norm_num
    linear_combination (709679/500000000000 : ℝ)*(base40) + (1401381/1000000000000 : ℝ)*(base50) + (104062485443/125000000000 : ℝ)*(base59) + (406611180557/125000000000 : ℝ)*(major_s3_0) + (406611180557/125000000000 : ℝ)*(major_s3_1) + (406611180557/125000000000 : ℝ)*(major_s3_2) + (1486507/500000000000 : ℝ)*(sp_s3_1) + (8383353/1000000000000 : ℝ)*(sp_s3_9) + (44606169/1000000000000 : ℝ)*(sp_s3_12) + (14566369/500000000000 : ℝ)*(sp_s3_15) + (4413186679957/1000000000000 : ℝ)*(sp_s3_19) + (2206591853471/500000000000 : ℝ)*(sp_s3_20) + (882629832773/200000000000 : ℝ)*(sp_s3_21) + (2092545484701/1000000000000 : ℝ)*(sp_s3_25) + (209259009087/100000000000 : ℝ)*(f.failure) + (4413186679957/1000000000000 : ℝ)*(f.sum) + (344163605134400357/2755907250000000000000000000000 : ℝ)*base62 + (613701223151101/755250000000000000000000000 : ℝ)*base65 + (1698454711180529/3466550000000000000000000000 : ℝ)*base67 + (476818382783317/755250000000000000000000000 : ℝ)*base69 + (34861568050484940841/52384895250000000000000000000000 : ℝ)*base71 + (29838263124683/69361000000000000000000000 : ℝ)*base73 + (1826907302545903/3466550000000000000000000000 : ℝ)*base75 + (3901134509166921/3468050000000000000000000000 : ℝ)*base77 + (16563462498567787181/240443374550000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (503/1250000000000000 : ℝ)*base86 + (503/1250000000000000 : ℝ)*base88 + (503/1250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((69361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69331/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3021/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3021/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4623/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4623/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36981/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36981/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4913/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4913/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307057_s3 p hpa hpb X hX hprev2

#print axioms solution

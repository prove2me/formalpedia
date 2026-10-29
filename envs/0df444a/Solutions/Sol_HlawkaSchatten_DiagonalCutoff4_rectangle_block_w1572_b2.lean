-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1572_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:56.194414+00:00
-- url     : https://prove2.me/submissions/68344502-7d47-4804-9f5c-043def7c8054

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1572_s6_0 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348066659/10000000000 : ℝ)*x 0 + (2610067657/5000000000 : ℝ)*x 1 + (-1887959217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348066659/10000000000 : ℝ)^4641 ≤ (44796829478203/100000000000000 : ℝ)^3617 := by
    have hnat : (5348066659 : ℕ)^4641*100000000000000^3617 ≤ 44796829478203^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348066659 10000000000 44796829478203 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610067657/5000000000 : ℝ)^4641 ≤ (2714159424479/6250000000000 : ℝ)^3617 := by
    have hnat : (2610067657 : ℕ)^4641*6250000000000^3617 ≤ 2714159424479^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610067657 5000000000 2714159424479 6250000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887959217/10000000000 : ℝ)^4641 ≤ (11776619721849/100000000000000 : ℝ)^3617 := by
    have hnat : (1887959217 : ℕ)^4641*100000000000000^3617 ≤ 11776619721849^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887959217 10000000000 11776619721849 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348066659/10000000000 : ℝ), (2610067657/5000000000 : ℝ), (-1887959217/10000000000 : ℝ)] ![(44796829478203/100000000000000 : ℝ), (2714159424479/6250000000000 : ℝ), (11776619721849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348066659/10000000000 : ℝ)|^4641 ≤ (44796829478203/100000000000000 : ℝ)^3617
        have hw : |(5348066659/10000000000 : ℝ)|=(5348066659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610067657/5000000000 : ℝ)|^4641 ≤ (2714159424479/6250000000000 : ℝ)^3617
        have hw : |(2610067657/5000000000 : ℝ)|=(2610067657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1887959217/10000000000 : ℝ)|^4641 ≤ (11776619721849/100000000000000 : ℝ)^3617
        have hw : |(-1887959217/10000000000 : ℝ)|=(1887959217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s6_1 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1782912003/10000000000 : ℝ)*x 0 + (5221205423/10000000000 : ℝ)*x 1 + (1084890673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1782912003/10000000000 : ℝ)^4641 ≤ (1367820620739/12500000000000 : ℝ)^3617 := by
    have hnat : (1782912003 : ℕ)^4641*12500000000000^3617 ≤ 1367820620739^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782912003 10000000000 1367820620739 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221205423/10000000000 : ℝ)^4641 ≤ (21718986857387/50000000000000 : ℝ)^3617 := by
    have hnat : (5221205423 : ℕ)^4641*50000000000000^3617 ≤ 21718986857387^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221205423 10000000000 21718986857387 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084890673/2000000000 : ℝ)^4641 ≤ (9123892263313/20000000000000 : ℝ)^3617 := by
    have hnat : (1084890673 : ℕ)^4641*20000000000000^3617 ≤ 9123892263313^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084890673 2000000000 9123892263313 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1782912003/10000000000 : ℝ), (5221205423/10000000000 : ℝ), (1084890673/2000000000 : ℝ)] ![(1367820620739/12500000000000 : ℝ), (21718986857387/50000000000000 : ℝ), (9123892263313/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1782912003/10000000000 : ℝ)|^4641 ≤ (1367820620739/12500000000000 : ℝ)^3617
        have hw : |(-1782912003/10000000000 : ℝ)|=(1782912003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221205423/10000000000 : ℝ)|^4641 ≤ (21718986857387/50000000000000 : ℝ)^3617
        have hw : |(5221205423/10000000000 : ℝ)|=(5221205423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084890673/2000000000 : ℝ)|^4641 ≤ (9123892263313/20000000000000 : ℝ)^3617
        have hw : |(1084890673/2000000000 : ℝ)|=(1084890673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s6_2 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293712297/10000000000 : ℝ)*x 0 + (-1683640997/10000000000 : ℝ)*x 1 + (5424453379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293712297/10000000000 : ℝ)^4641 ≤ (22106745147977/50000000000000 : ℝ)^3617 := by
    have hnat : (5293712297 : ℕ)^4641*50000000000000^3617 ≤ 22106745147977^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293712297 10000000000 22106745147977 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1683640997/10000000000 : ℝ)^4641 ≤ (10167048227013/100000000000000 : ℝ)^3617 := by
    have hnat : (1683640997 : ℕ)^4641*100000000000000^3617 ≤ 10167048227013^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683640997 10000000000 10167048227013 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424453379/10000000000 : ℝ)^4641 ≤ (45619461467637/100000000000000 : ℝ)^3617 := by
    have hnat : (5424453379 : ℕ)^4641*100000000000000^3617 ≤ 45619461467637^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424453379 10000000000 45619461467637 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293712297/10000000000 : ℝ), (-1683640997/10000000000 : ℝ), (5424453379/10000000000 : ℝ)] ![(22106745147977/50000000000000 : ℝ), (10167048227013/100000000000000 : ℝ), (45619461467637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293712297/10000000000 : ℝ)|^4641 ≤ (22106745147977/50000000000000 : ℝ)^3617
        have hw : |(5293712297/10000000000 : ℝ)|=(5293712297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1683640997/10000000000 : ℝ)|^4641 ≤ (10167048227013/100000000000000 : ℝ)^3617
        have hw : |(-1683640997/10000000000 : ℝ)|=(1683640997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424453379/10000000000 : ℝ)|^4641 ≤ (45619461467637/100000000000000 : ℝ)^3617
        have hw : |(5424453379/10000000000 : ℝ)|=(5424453379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s6_3 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293712297/10000000000 : ℝ)*x 0 + (5424453369/10000000000 : ℝ)*x 1 + (-168364101/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293712297/10000000000 : ℝ)^4641 ≤ (22106745147977/50000000000000 : ℝ)^3617 := by
    have hnat : (5293712297 : ℕ)^4641*50000000000000^3617 ≤ 22106745147977^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293712297 10000000000 22106745147977 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424453369/10000000000 : ℝ)^4641 ≤ (2851216334983/6250000000000 : ℝ)^3617 := by
    have hnat : (5424453369 : ℕ)^4641*6250000000000^3617 ≤ 2851216334983^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424453369 10000000000 2851216334983 6250000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168364101/1000000000 : ℝ)^4641 ≤ (10167048327741/100000000000000 : ℝ)^3617 := by
    have hnat : (168364101 : ℕ)^4641*100000000000000^3617 ≤ 10167048327741^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168364101 1000000000 10167048327741 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293712297/10000000000 : ℝ), (5424453369/10000000000 : ℝ), (-168364101/1000000000 : ℝ)] ![(22106745147977/50000000000000 : ℝ), (2851216334983/6250000000000 : ℝ), (10167048327741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293712297/10000000000 : ℝ)|^4641 ≤ (22106745147977/50000000000000 : ℝ)^3617
        have hw : |(5293712297/10000000000 : ℝ)|=(5293712297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424453369/10000000000 : ℝ)|^4641 ≤ (2851216334983/6250000000000 : ℝ)^3617
        have hw : |(5424453369/10000000000 : ℝ)|=(5424453369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168364101/1000000000 : ℝ)|^4641 ≤ (10167048327741/100000000000000 : ℝ)^3617
        have hw : |(-168364101/1000000000 : ℝ)|=(168364101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s6_4 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530336173/1250000000 : ℝ)*x 0 + (4488467869/10000000000 : ℝ)*x 1 + (4008034763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530336173/1250000000 : ℝ)^4641 ≤ (33283091672119/100000000000000 : ℝ)^3617 := by
    have hnat : (530336173 : ℕ)^4641*100000000000000^3617 ≤ 33283091672119^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530336173 1250000000 33283091672119 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488467869/10000000000 : ℝ)^4641 ≤ (35777045450641/100000000000000 : ℝ)^3617 := by
    have hnat : (4488467869 : ℕ)^4641*100000000000000^3617 ≤ 35777045450641^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488467869 10000000000 35777045450641 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4008034763/10000000000 : ℝ)^4641 ≤ (247518903007/800000000000 : ℝ)^3617 := by
    have hnat : (4008034763 : ℕ)^4641*800000000000^3617 ≤ 247518903007^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008034763 10000000000 247518903007 800000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530336173/1250000000 : ℝ), (4488467869/10000000000 : ℝ), (4008034763/10000000000 : ℝ)] ![(33283091672119/100000000000000 : ℝ), (35777045450641/100000000000000 : ℝ), (247518903007/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530336173/1250000000 : ℝ)|^4641 ≤ (33283091672119/100000000000000 : ℝ)^3617
        have hw : |(530336173/1250000000 : ℝ)|=(530336173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488467869/10000000000 : ℝ)|^4641 ≤ (35777045450641/100000000000000 : ℝ)^3617
        have hw : |(4488467869/10000000000 : ℝ)|=(4488467869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4008034763/10000000000 : ℝ)|^4641 ≤ (247518903007/800000000000 : ℝ)^3617
        have hw : |(4008034763/10000000000 : ℝ)|=(4008034763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1572_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1391/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1391/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1391/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1391/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1391/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1391/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1391/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (1391/12500 : ℝ) ^ (4639/1024 : ℝ) ≤ (299149865531609/6250000000000000000 : ℝ) := by
    have hpowers : (1391/12500 : ℝ)^4639 ≤ (299149865531609/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1391 : ℕ)^4639*6250000000000000000^1024 ≤ 299149865531609^1024*12500^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1391 12500 299149865531609 6250000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1391/12500 : ℝ)) (X := (299149865531609/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4639/1024 : ℝ) ≤ (10691687968153991/50000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4639 ≤ (10691687968153991/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4639*50000000000000000000^1024 ≤ 10691687968153991^1024*20000^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 10691687968153991 50000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (10691687968153991/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125299149865531609/3125000000000000000 : ℝ) ≤ (5000105649678737/5000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (3125299149865531609/3125000000000000000 : ℝ)^1024 ≤ (5000105649678737/5000000000000000 : ℝ)^4639 := by
      have hnat : (3125299149865531609 : ℕ)^1024*5000000000000000^4639 ≤ 5000105649678737^4639*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125299149865531609 3125000000000000000 5000105649678737 5000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000105649678737/5000000000000000 : ℝ)) (X := (3125299149865531609/3125000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013084886892406863/50000000000000000000 : ℝ) ≤ (2000115521087819/2000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (50013084886892406863/50000000000000000000 : ℝ)^1024 ≤ (2000115521087819/2000000000000000 : ℝ)^4639 := by
      have hnat : (50013084886892406863 : ℕ)^1024*2000000000000000^4639 ≤ 2000115521087819^4639*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013084886892406863 50000000000000000000 2000115521087819 2000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000115521087819/2000000000000000 : ℝ)) (X := (50013084886892406863/50000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010691687968153991/25000000000000000000 : ℝ) ≤ (2500235977880179/2500000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (25010691687968153991/25000000000000000000 : ℝ)^1024 ≤ (2500235977880179/2500000000000000 : ℝ)^4639 := by
      have hnat : (25010691687968153991 : ℕ)^1024*2500000000000000^4639 ≤ 2500235977880179^4639*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010691687968153991 25000000000000000000 2500235977880179 2500000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500235977880179/2500000000000000 : ℝ)) (X := (25010691687968153991/25000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(299149865531609/6250000000000000000 : ℝ) ≤ ((21781384061573978621/21785000000000000000 : ℝ)+2*(366306081621/435700000000000 : ℝ)*(1391/12500 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (21781384061573978621/21785000000000000000 : ℝ)+2*(366306081621/435700000000000 : ℝ)*(1391/12500 : ℝ)=(5000105649678737/5000000000000000 : ℝ) by norm_num, show 1+2*(299149865531609/6250000000000000000 : ℝ)=(3125299149865531609/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10691687968153991/50000000000000000000 : ℝ)+(299149865531609/6250000000000000000 : ℝ) ≤ ((21781384061573978621/21785000000000000000 : ℝ)+(366306081621/435700000000000 : ℝ)*((3097/20000 : ℝ)+(1391/12500 : ℝ)))^(4639/1024 : ℝ) := by
    rw [show (21781384061573978621/21785000000000000000 : ℝ)+(366306081621/435700000000000 : ℝ)*((3097/20000 : ℝ)+(1391/12500 : ℝ))=(2000115521087819/2000000000000000 : ℝ) by norm_num, show 1+(10691687968153991/50000000000000000000 : ℝ)+(299149865531609/6250000000000000000 : ℝ)=(50013084886892406863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10691687968153991/50000000000000000000 : ℝ) ≤ ((21781384061573978621/21785000000000000000 : ℝ)+2*(366306081621/435700000000000 : ℝ)*(3097/20000 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (21781384061573978621/21785000000000000000 : ℝ)+2*(366306081621/435700000000000 : ℝ)*(3097/20000 : ℝ)=(2500235977880179/2500000000000000 : ℝ) by norm_num, show 1+2*(10691687968153991/50000000000000000000 : ℝ)=(25010691687968153991/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21781384061573978621/21785000000000000000 : ℝ)*(X 1 0+X 2 0)+(366306081621/435700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21781384061573978621/21785000000000000000 : ℝ)) (alpha := (366306081621/435700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21781384061573978621/21785000000000000000 : ℝ)*(X 0 1+X 2 1)+(366306081621/435700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21781384061573978621/21785000000000000000 : ℝ)) (alpha := (366306081621/435700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21781384061573978621/21785000000000000000 : ℝ)*(X 0 2+X 1 2)+(366306081621/435700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21781384061573978621/21785000000000000000 : ℝ)) (alpha := (366306081621/435700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5348066659/10000000000 : ℝ)*X 2 0+(2610067657/5000000000 : ℝ)*X 2 1+(-1887959217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1782912003/10000000000 : ℝ)*X 0 0+(5221205423/10000000000 : ℝ)*X 0 1+(1084890673/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5293712297/10000000000 : ℝ)*X 1 0+(-1683640997/10000000000 : ℝ)*X 1 1+(5424453379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5293712297/10000000000 : ℝ)*X 2 0+(5424453369/10000000000 : ℝ)*X 2 1+(-168364101/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((530336173/1250000000 : ℝ)*X 0 0+(4488467869/10000000000 : ℝ)*X 0 1+(4008034763/10000000000 : ℝ)*X 0 2+(530336173/1250000000 : ℝ)*X 1 0+(4488467869/10000000000 : ℝ)*X 1 1+(4008034763/10000000000 : ℝ)*X 1 2+(530336173/1250000000 : ℝ)*X 2 0+(4488467869/10000000000 : ℝ)*X 2 1+(4008034763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (152421110036632432209891207/34039062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (69762451/10000000000000 : ℝ)*(base19) + (374281939/50000000000000 : ℝ)*(base23) + (58957567/25000000000000 : ℝ)*(lower1) + (90259207/100000000000000 : ℝ)*(upper3) + (4969171/20000000000000 : ℝ)*(lower4) + (92465677/100000000000000 : ℝ)*(upper5) + (218798041043611/6250000000000 : ℝ)*(major0) + (218798041043611/6250000000000 : ℝ)*(major1) + (218798041043611/6250000000000 : ℝ)*(major2) + (390030423/100000000000000 : ℝ)*(sp0) + (4920087011644861/100000000000000 : ℝ)*(sp1) + (4920086314020351/100000000000000 : ℝ)*(sp2) + (15375268353283/312500000000 : ℝ)*(sp3) + (520362538122423/25000000000000 : ℝ)*(sp4) + (520362538122423/25000000000000 : ℝ)*(f.failure) + (4920087011644861/100000000000000 : ℝ)*(f.sum) + (100928243561071/21785000000000000000000000000 : ℝ)*base65 + (2370247211048346681/136156250000000000000000000000000 : ℝ)*base67 + (2326461715189909181/136156250000000000000000000000000 : ℝ)*base69 + (6184569460005596681/136156250000000000000000000000000 : ℝ)*base71 + (98921556279111/21785000000000000000000000000 : ℝ)*base73 + (10819846550041534181/136156250000000000000000000000000 : ℝ)*base75 + (81306694316590819/136156250000000000000000000000000 : ℝ)*base78 + (2542796221377627931/136156250000000000000000000000000 : ℝ)*base79 + (233059160164971/21785000000000000000000000000 : ℝ)*base81 + (9556151/1250000000000000000000 : ℝ)*base90 + (9556151/1250000000000000000000 : ℝ)*base92 + (9556151/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1572_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1572_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1572_box_0 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1579403939/10000000000 : ℝ)*x 0 + (1349094251/2500000000 : ℝ)*x 1 + (1349094259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1579403939/10000000000 : ℝ)^4641 ≤ (9366570298279/100000000000000 : ℝ)^3617 := by
    have hnat : (1579403939 : ℕ)^4641*100000000000000^3617 ≤ 9366570298279^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579403939 10000000000 9366570298279 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349094251/2500000000 : ℝ)^4641 ≤ (45316714666671/100000000000000 : ℝ)^3617 := by
    have hnat : (1349094251 : ℕ)^4641*100000000000000^3617 ≤ 45316714666671^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349094251 2500000000 45316714666671 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349094259/2500000000 : ℝ)^4641 ≤ (45316715011473/100000000000000 : ℝ)^3617 := by
    have hnat : (1349094259 : ℕ)^4641*100000000000000^3617 ≤ 45316715011473^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349094259 2500000000 45316715011473 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1579403939/10000000000 : ℝ), (1349094251/2500000000 : ℝ), (1349094259/2500000000 : ℝ)] ![(9366570298279/100000000000000 : ℝ), (45316714666671/100000000000000 : ℝ), (45316715011473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1579403939/10000000000 : ℝ)|^4641 ≤ (9366570298279/100000000000000 : ℝ)^3617
        have hw : |(-1579403939/10000000000 : ℝ)|=(1579403939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349094251/2500000000 : ℝ)|^4641 ≤ (45316714666671/100000000000000 : ℝ)^3617
        have hw : |(1349094251/2500000000 : ℝ)|=(1349094251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349094259/2500000000 : ℝ)|^4641 ≤ (45316715011473/100000000000000 : ℝ)^3617
        have hw : |(1349094259/2500000000 : ℝ)|=(1349094259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_1 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271143337/10000000000 : ℝ)*x 0 + (-438375503/2500000000 : ℝ)*x 1 + (5396377783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271143337/10000000000 : ℝ)^4641 ≤ (21985886804931/50000000000000 : ℝ)^3617 := by
    have hnat : (5271143337 : ℕ)^4641*50000000000000^3617 ≤ 21985886804931^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271143337 10000000000 21985886804931 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438375503/2500000000 : ℝ)^4641 ≤ (1338937913941/12500000000000 : ℝ)^3617 := by
    have hnat : (438375503 : ℕ)^4641*12500000000000^3617 ≤ 1338937913941^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438375503 2500000000 1338937913941 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396377783/10000000000 : ℝ)^4641 ≤ (45316723060433/100000000000000 : ℝ)^3617 := by
    have hnat : (5396377783 : ℕ)^4641*100000000000000^3617 ≤ 45316723060433^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396377783 10000000000 45316723060433 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271143337/10000000000 : ℝ), (-438375503/2500000000 : ℝ), (5396377783/10000000000 : ℝ)] ![(21985886804931/50000000000000 : ℝ), (1338937913941/12500000000000 : ℝ), (45316723060433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271143337/10000000000 : ℝ)|^4641 ≤ (21985886804931/50000000000000 : ℝ)^3617
        have hw : |(5271143337/10000000000 : ℝ)|=(5271143337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438375503/2500000000 : ℝ)|^4641 ≤ (1338937913941/12500000000000 : ℝ)^3617
        have hw : |(-438375503/2500000000 : ℝ)|=(438375503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396377783/10000000000 : ℝ)|^4641 ≤ (45316723060433/100000000000000 : ℝ)^3617
        have hw : |(5396377783/10000000000 : ℝ)|=(5396377783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_2 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329446483/625000000 : ℝ)*x 0 + (337273609/625000000 : ℝ)*x 1 + (-1753501533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329446483/625000000 : ℝ)^4641 ≤ (2748236112187/6250000000000 : ℝ)^3617 := by
    have hnat : (329446483 : ℕ)^4641*6250000000000^3617 ≤ 2748236112187^3617*625000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329446483 625000000 2748236112187 6250000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337273609/625000000 : ℝ)^4641 ≤ (45316722640207/100000000000000 : ℝ)^3617 := by
    have hnat : (337273609 : ℕ)^4641*100000000000000^3617 ≤ 45316722640207^3617*625000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337273609 625000000 45316722640207 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1753501533/10000000000 : ℝ)^4641 ≤ (10711499557109/100000000000000 : ℝ)^3617 := by
    have hnat : (1753501533 : ℕ)^4641*100000000000000^3617 ≤ 10711499557109^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1753501533 10000000000 10711499557109 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329446483/625000000 : ℝ), (337273609/625000000 : ℝ), (-1753501533/10000000000 : ℝ)] ![(2748236112187/6250000000000 : ℝ), (45316722640207/100000000000000 : ℝ), (10711499557109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329446483/625000000 : ℝ)|^4641 ≤ (2748236112187/6250000000000 : ℝ)^3617
        have hw : |(329446483/625000000 : ℝ)|=(329446483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337273609/625000000 : ℝ)|^4641 ≤ (45316722640207/100000000000000 : ℝ)^3617
        have hw : |(337273609/625000000 : ℝ)|=(337273609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1753501533/10000000000 : ℝ)|^4641 ≤ (10711499557109/100000000000000 : ℝ)^3617
        have hw : |(-1753501533/10000000000 : ℝ)|=(1753501533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_3 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4443235421/10000000000 : ℝ)*x 0 + (518618087/1250000000 : ℝ)*x 1 + (103723639/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4443235421/10000000000 : ℝ)^4641 ≤ (4414386523591/12500000000000 : ℝ)^3617 := by
    have hnat : (4443235421 : ℕ)^4641*12500000000000^3617 ≤ 4414386523591^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4443235421 10000000000 4414386523591 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518618087/1250000000 : ℝ)^4641 ≤ (32342449576141/100000000000000 : ℝ)^3617 := by
    have hnat : (518618087 : ℕ)^4641*100000000000000^3617 ≤ 32342449576141^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518618087 1250000000 32342449576141 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103723639/250000000 : ℝ)^4641 ≤ (32342458218097/100000000000000 : ℝ)^3617 := by
    have hnat : (103723639 : ℕ)^4641*100000000000000^3617 ≤ 32342458218097^3617*250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103723639 250000000 32342458218097 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4443235421/10000000000 : ℝ), (518618087/1250000000 : ℝ), (103723639/250000000 : ℝ)] ![(4414386523591/12500000000000 : ℝ), (32342449576141/100000000000000 : ℝ), (32342458218097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4443235421/10000000000 : ℝ)|^4641 ≤ (4414386523591/12500000000000 : ℝ)^3617
        have hw : |(4443235421/10000000000 : ℝ)|=(4443235421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518618087/1250000000 : ℝ)|^4641 ≤ (32342449576141/100000000000000 : ℝ)^3617
        have hw : |(518618087/1250000000 : ℝ)|=(518618087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103723639/250000000 : ℝ)|^4641 ≤ (32342458218097/100000000000000 : ℝ)^3617
        have hw : |(103723639/250000000 : ℝ)|=(103723639/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_4 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-995879437/5000000000 : ℝ)*x 0 + (1311272631/2500000000 : ℝ)*x 1 + (5245090397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (995879437/5000000000 : ℝ)^4641 ≤ (39418075799/312500000000 : ℝ)^3617 := by
    have hnat : (995879437 : ℕ)^4641*312500000000^3617 ≤ 39418075799^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995879437 5000000000 39418075799 312500000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311272631/2500000000 : ℝ)^4641 ≤ (43693108545527/100000000000000 : ℝ)^3617 := by
    have hnat : (1311272631 : ℕ)^4641*100000000000000^3617 ≤ 43693108545527^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311272631 2500000000 43693108545527 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245090397/10000000000 : ℝ)^4641 ≤ (10923276797017/25000000000000 : ℝ)^3617 := by
    have hnat : (5245090397 : ℕ)^4641*25000000000000^3617 ≤ 10923276797017^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245090397 10000000000 10923276797017 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-995879437/5000000000 : ℝ), (1311272631/2500000000 : ℝ), (5245090397/10000000000 : ℝ)] ![(39418075799/312500000000 : ℝ), (43693108545527/100000000000000 : ℝ), (10923276797017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-995879437/5000000000 : ℝ)|^4641 ≤ (39418075799/312500000000 : ℝ)^3617
        have hw : |(-995879437/5000000000 : ℝ)|=(995879437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311272631/2500000000 : ℝ)|^4641 ≤ (43693108545527/100000000000000 : ℝ)^3617
        have hw : |(1311272631/2500000000 : ℝ)|=(1311272631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245090397/10000000000 : ℝ)|^4641 ≤ (10923276797017/25000000000000 : ℝ)^3617
        have hw : |(5245090397/10000000000 : ℝ)|=(5245090397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_5 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375996713/10000000000 : ℝ)*x 0 + (-908369017/5000000000 : ℝ)*x 1 + (2622545247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375996713/10000000000 : ℝ)^4641 ≤ (45097233566479/100000000000000 : ℝ)^3617 := by
    have hnat : (5375996713 : ℕ)^4641*100000000000000^3617 ≤ 45097233566479^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375996713 10000000000 45097233566479 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908369017/5000000000 : ℝ)^4641 ≤ (700603637131/6250000000000 : ℝ)^3617 := by
    have hnat : (908369017 : ℕ)^4641*6250000000000^3617 ≤ 700603637131^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908369017 5000000000 700603637131 6250000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622545247/5000000000 : ℝ)^4641 ≤ (43693108224867/100000000000000 : ℝ)^3617 := by
    have hnat : (2622545247 : ℕ)^4641*100000000000000^3617 ≤ 43693108224867^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622545247 5000000000 43693108224867 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375996713/10000000000 : ℝ), (-908369017/5000000000 : ℝ), (2622545247/5000000000 : ℝ)] ![(45097233566479/100000000000000 : ℝ), (700603637131/6250000000000 : ℝ), (43693108224867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375996713/10000000000 : ℝ)|^4641 ≤ (45097233566479/100000000000000 : ℝ)^3617
        have hw : |(5375996713/10000000000 : ℝ)|=(5375996713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-908369017/5000000000 : ℝ)|^4641 ≤ (700603637131/6250000000000 : ℝ)^3617
        have hw : |(-908369017/5000000000 : ℝ)|=(908369017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622545247/5000000000 : ℝ)|^4641 ≤ (43693108224867/100000000000000 : ℝ)^3617
        have hw : |(2622545247/5000000000 : ℝ)|=(2622545247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_6 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375996837/10000000000 : ℝ)*x 0 + (524509049/1000000000 : ℝ)*x 1 + (-181673787/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375996837/10000000000 : ℝ)^4641 ≤ (9019446980231/20000000000000 : ℝ)^3617 := by
    have hnat : (5375996837 : ℕ)^4641*20000000000000^3617 ≤ 9019446980231^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375996837 10000000000 9019446980231 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524509049/1000000000 : ℝ)^4641 ≤ (1365409630691/3125000000000 : ℝ)^3617 := by
    have hnat : (524509049 : ℕ)^4641*3125000000000^3617 ≤ 1365409630691^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524509049 1000000000 1365409630691 3125000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181673787/1000000000 : ℝ)^4641 ≤ (11209656895701/100000000000000 : ℝ)^3617 := by
    have hnat : (181673787 : ℕ)^4641*100000000000000^3617 ≤ 11209656895701^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181673787 1000000000 11209656895701 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375996837/10000000000 : ℝ), (524509049/1000000000 : ℝ), (-181673787/1000000000 : ℝ)] ![(9019446980231/20000000000000 : ℝ), (1365409630691/3125000000000 : ℝ), (11209656895701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375996837/10000000000 : ℝ)|^4641 ≤ (9019446980231/20000000000000 : ℝ)^3617
        have hw : |(5375996837/10000000000 : ℝ)|=(5375996837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524509049/1000000000 : ℝ)|^4641 ≤ (1365409630691/3125000000000 : ℝ)^3617
        have hw : |(524509049/1000000000 : ℝ)|=(524509049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-181673787/1000000000 : ℝ)|^4641 ≤ (11209656895701/100000000000000 : ℝ)^3617
        have hw : |(-181673787/1000000000 : ℝ)|=(181673787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_7 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4039315953/10000000000 : ℝ)*x 0 + (13596179/31250000 : ℝ)*x 1 + (217538899/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4039315953/10000000000 : ℝ)^4641 ≤ (6250008300977/20000000000000 : ℝ)^3617 := by
    have hnat : (4039315953 : ℕ)^4641*20000000000000^3617 ≤ 6250008300977^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039315953 10000000000 6250008300977 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13596179/31250000 : ℝ)^4641 ≤ (3437497569433/10000000000000 : ℝ)^3617 := by
    have hnat : (13596179 : ℕ)^4641*10000000000000^3617 ≤ 3437497569433^3617*31250000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13596179 31250000 3437497569433 10000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217538899/500000000 : ℝ)^4641 ≤ (17187491395353/50000000000000 : ℝ)^3617 := by
    have hnat : (217538899 : ℕ)^4641*50000000000000^3617 ≤ 17187491395353^3617*500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217538899 500000000 17187491395353 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4039315953/10000000000 : ℝ), (13596179/31250000 : ℝ), (217538899/500000000 : ℝ)] ![(6250008300977/20000000000000 : ℝ), (3437497569433/10000000000000 : ℝ), (17187491395353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4039315953/10000000000 : ℝ)|^4641 ≤ (6250008300977/20000000000000 : ℝ)^3617
        have hw : |(4039315953/10000000000 : ℝ)|=(4039315953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13596179/31250000 : ℝ)|^4641 ≤ (3437497569433/10000000000000 : ℝ)^3617
        have hw : |(13596179/31250000 : ℝ)|=(13596179/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217538899/500000000 : ℝ)|^4641 ≤ (17187491395353/50000000000000 : ℝ)^3617
        have hw : |(217538899/500000000 : ℝ)|=(217538899/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_8 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-952172859/5000000000 : ℝ)*x 0 + (5138481667/10000000000 : ℝ)*x 1 + (5416640317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952172859/5000000000 : ℝ)^4641 ≤ (11907933253709/100000000000000 : ℝ)^3617 := by
    have hnat : (952172859 : ℕ)^4641*100000000000000^3617 ≤ 11907933253709^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952172859 5000000000 11907933253709 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138481667/10000000000 : ℝ)^4641 ≤ (21278448977497/50000000000000 : ℝ)^3617 := by
    have hnat : (5138481667 : ℕ)^4641*50000000000000^3617 ≤ 21278448977497^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138481667 10000000000 21278448977497 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416640317/10000000000 : ℝ)^4641 ≤ (22767584388429/50000000000000 : ℝ)^3617 := by
    have hnat : (5416640317 : ℕ)^4641*50000000000000^3617 ≤ 22767584388429^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416640317 10000000000 22767584388429 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952172859/5000000000 : ℝ), (5138481667/10000000000 : ℝ), (5416640317/10000000000 : ℝ)] ![(11907933253709/100000000000000 : ℝ), (21278448977497/50000000000000 : ℝ), (22767584388429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952172859/5000000000 : ℝ)|^4641 ≤ (11907933253709/100000000000000 : ℝ)^3617
        have hw : |(-952172859/5000000000 : ℝ)|=(952172859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138481667/10000000000 : ℝ)|^4641 ≤ (21278448977497/50000000000000 : ℝ)^3617
        have hw : |(5138481667/10000000000 : ℝ)|=(5138481667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416640317/10000000000 : ℝ)|^4641 ≤ (22767584388429/50000000000000 : ℝ)^3617
        have hw : |(5416640317/10000000000 : ℝ)|=(5416640317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_9 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628548271/5000000000 : ℝ)*x 0 + (-436200133/2500000000 : ℝ)*x 1 + (84635011/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628548271/5000000000 : ℝ)^4641 ≤ (10955369568641/25000000000000 : ℝ)^3617 := by
    have hnat : (2628548271 : ℕ)^4641*25000000000000^3617 ≤ 10955369568641^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628548271 5000000000 10955369568641 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436200133/2500000000 : ℝ)^4641 ≤ (532167438437/5000000000000 : ℝ)^3617 := by
    have hnat : (436200133 : ℕ)^4641*5000000000000^3617 ≤ 532167438437^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436200133 2500000000 532167438437 5000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84635011/156250000 : ℝ)^4641 ≤ (11383793237807/25000000000000 : ℝ)^3617 := by
    have hnat : (84635011 : ℕ)^4641*25000000000000^3617 ≤ 11383793237807^3617*156250000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84635011 156250000 11383793237807 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628548271/5000000000 : ℝ), (-436200133/2500000000 : ℝ), (84635011/156250000 : ℝ)] ![(10955369568641/25000000000000 : ℝ), (532167438437/5000000000000 : ℝ), (11383793237807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628548271/5000000000 : ℝ)|^4641 ≤ (10955369568641/25000000000000 : ℝ)^3617
        have hw : |(2628548271/5000000000 : ℝ)|=(2628548271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436200133/2500000000 : ℝ)|^4641 ≤ (532167438437/5000000000000 : ℝ)^3617
        have hw : |(-436200133/2500000000 : ℝ)|=(436200133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84635011/156250000 : ℝ)|^4641 ≤ (11383793237807/25000000000000 : ℝ)^3617
        have hw : |(84635011/156250000 : ℝ)|=(84635011/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_10 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131427407/250000000 : ℝ)*x 0 + (67708009/125000000 : ℝ)*x 1 + (-872400433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131427407/250000000 : ℝ)^4641 ≤ (10955368868081/25000000000000 : ℝ)^3617 := by
    have hnat : (131427407 : ℕ)^4641*25000000000000^3617 ≤ 10955368868081^3617*250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131427407 250000000 10955368868081 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67708009/125000000 : ℝ)^4641 ≤ (11383793280953/25000000000000 : ℝ)^3617 := by
    have hnat : (67708009 : ℕ)^4641*25000000000000^3617 ≤ 11383793280953^3617*125000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67708009 125000000 11383793280953 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (872400433/5000000000 : ℝ)^4641 ≤ (133041892287/1250000000000 : ℝ)^3617 := by
    have hnat : (872400433 : ℕ)^4641*1250000000000^3617 ≤ 133041892287^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872400433 5000000000 133041892287 1250000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131427407/250000000 : ℝ), (67708009/125000000 : ℝ), (-872400433/5000000000 : ℝ)] ![(10955368868081/25000000000000 : ℝ), (11383793280953/25000000000000 : ℝ), (133041892287/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131427407/250000000 : ℝ)|^4641 ≤ (10955368868081/25000000000000 : ℝ)^3617
        have hw : |(131427407/250000000 : ℝ)|=(131427407/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67708009/125000000 : ℝ)|^4641 ≤ (11383793280953/25000000000000 : ℝ)^3617
        have hw : |(67708009/125000000 : ℝ)|=(67708009/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-872400433/5000000000 : ℝ)|^4641 ≤ (133041892287/1250000000000 : ℝ)^3617
        have hw : |(-872400433/5000000000 : ℝ)|=(872400433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_11 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1124048537/2500000000 : ℝ)*x 0 + (32975009/80000000 : ℝ)*x 1 + (4121877003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124048537/2500000000 : ℝ)^4641 ≤ (717121704037/2000000000000 : ℝ)^3617 := by
    have hnat : (1124048537 : ℕ)^4641*2000000000000^3617 ≤ 717121704037^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124048537 2500000000 717121704037 2000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32975009/80000000 : ℝ)^4641 ≤ (8017988252313/25000000000000 : ℝ)^3617 := by
    have hnat : (32975009 : ℕ)^4641*25000000000000^3617 ≤ 8017988252313^3617*80000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32975009 80000000 8017988252313 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4121877003/10000000000 : ℝ)^4641 ≤ (32071961774981/100000000000000 : ℝ)^3617 := by
    have hnat : (4121877003 : ℕ)^4641*100000000000000^3617 ≤ 32071961774981^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121877003 10000000000 32071961774981 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1124048537/2500000000 : ℝ), (32975009/80000000 : ℝ), (4121877003/10000000000 : ℝ)] ![(717121704037/2000000000000 : ℝ), (8017988252313/25000000000000 : ℝ), (32071961774981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1124048537/2500000000 : ℝ)|^4641 ≤ (717121704037/2000000000000 : ℝ)^3617
        have hw : |(1124048537/2500000000 : ℝ)|=(1124048537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32975009/80000000 : ℝ)|^4641 ≤ (8017988252313/25000000000000 : ℝ)^3617
        have hw : |(32975009/80000000 : ℝ)|=(32975009/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4121877003/10000000000 : ℝ)|^4641 ≤ (32071961774981/100000000000000 : ℝ)^3617
        have hw : |(4121877003/10000000000 : ℝ)|=(4121877003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_12 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-833235167/5000000000 : ℝ)*x 0 + (1099948433/2000000000 : ℝ)*x 1 + (2615020649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833235167/5000000000 : ℝ)^4641 ≤ (1254274587119/12500000000000 : ℝ)^3617 := by
    have hnat : (833235167 : ℕ)^4641*12500000000000^3617 ≤ 1254274587119^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833235167 5000000000 1254274587119 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099948433/2000000000 : ℝ)^4641 ≤ (46433485337109/100000000000000 : ℝ)^3617 := by
    have hnat : (1099948433 : ℕ)^4641*100000000000000^3617 ≤ 46433485337109^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099948433 2000000000 46433485337109 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615020649/5000000000 : ℝ)^4641 ≤ (10883079488267/25000000000000 : ℝ)^3617 := by
    have hnat : (2615020649 : ℕ)^4641*25000000000000^3617 ≤ 10883079488267^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615020649 5000000000 10883079488267 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-833235167/5000000000 : ℝ), (1099948433/2000000000 : ℝ), (2615020649/5000000000 : ℝ)] ![(1254274587119/12500000000000 : ℝ), (46433485337109/100000000000000 : ℝ), (10883079488267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-833235167/5000000000 : ℝ)|^4641 ≤ (1254274587119/12500000000000 : ℝ)^3617
        have hw : |(-833235167/5000000000 : ℝ)|=(833235167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099948433/2000000000 : ℝ)|^4641 ≤ (46433485337109/100000000000000 : ℝ)^3617
        have hw : |(1099948433/2000000000 : ℝ)|=(1099948433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615020649/5000000000 : ℝ)|^4641 ≤ (10883079488267/25000000000000 : ℝ)^3617
        have hw : |(2615020649/5000000000 : ℝ)|=(2615020649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_13 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386428763/10000000000 : ℝ)*x 0 + (-911429213/5000000000 : ℝ)*x 1 + (653755109/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386428763/10000000000 : ℝ)^4641 ≤ (2260477494101/5000000000000 : ℝ)^3617 := by
    have hnat : (5386428763 : ℕ)^4641*5000000000000^3617 ≤ 2260477494101^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386428763 10000000000 2260477494101 5000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (911429213/5000000000 : ℝ)^4641 ≤ (2251627340537/20000000000000 : ℝ)^3617 := by
    have hnat : (911429213 : ℕ)^4641*20000000000000^3617 ≤ 2251627340537^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911429213 5000000000 2251627340537 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653755109/1250000000 : ℝ)^4641 ≤ (10883078350851/25000000000000 : ℝ)^3617 := by
    have hnat : (653755109 : ℕ)^4641*25000000000000^3617 ≤ 10883078350851^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653755109 1250000000 10883078350851 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386428763/10000000000 : ℝ), (-911429213/5000000000 : ℝ), (653755109/1250000000 : ℝ)] ![(2260477494101/5000000000000 : ℝ), (2251627340537/20000000000000 : ℝ), (10883078350851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386428763/10000000000 : ℝ)|^4641 ≤ (2260477494101/5000000000000 : ℝ)^3617
        have hw : |(5386428763/10000000000 : ℝ)|=(5386428763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-911429213/5000000000 : ℝ)|^4641 ≤ (2251627340537/20000000000000 : ℝ)^3617
        have hw : |(-911429213/5000000000 : ℝ)|=(911429213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653755109/1250000000 : ℝ)|^4641 ≤ (10883078350851/25000000000000 : ℝ)^3617
        have hw : |(653755109/1250000000 : ℝ)|=(653755109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_14 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386428387/10000000000 : ℝ)*x 0 + (5230041439/10000000000 : ℝ)*x 1 + (-1822858173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386428387/10000000000 : ℝ)^4641 ≤ (22604772916359/50000000000000 : ℝ)^3617 := by
    have hnat : (5386428387 : ℕ)^4641*50000000000000^3617 ≤ 22604772916359^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386428387 10000000000 22604772916359 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230041439/10000000000 : ℝ)^4641 ≤ (43532319458943/100000000000000 : ℝ)^3617 := by
    have hnat : (5230041439 : ℕ)^4641*100000000000000^3617 ≤ 43532319458943^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230041439 10000000000 43532319458943 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1822858173/10000000000 : ℝ)^4641 ≤ (2251626939553/20000000000000 : ℝ)^3617 := by
    have hnat : (1822858173 : ℕ)^4641*20000000000000^3617 ≤ 2251626939553^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822858173 10000000000 2251626939553 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386428387/10000000000 : ℝ), (5230041439/10000000000 : ℝ), (-1822858173/10000000000 : ℝ)] ![(22604772916359/50000000000000 : ℝ), (43532319458943/100000000000000 : ℝ), (2251626939553/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386428387/10000000000 : ℝ)|^4641 ≤ (22604772916359/50000000000000 : ℝ)^3617
        have hw : |(5386428387/10000000000 : ℝ)|=(5386428387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230041439/10000000000 : ℝ)|^4641 ≤ (43532319458943/100000000000000 : ℝ)^3617
        have hw : |(5230041439/10000000000 : ℝ)|=(5230041439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1822858173/10000000000 : ℝ)|^4641 ≤ (2251626939553/20000000000000 : ℝ)^3617
        have hw : |(-1822858173/10000000000 : ℝ)|=(1822858173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_box_15 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1999135781/5000000000 : ℝ)*x 0 + (4370830339/10000000000 : ℝ)*x 1 + (4370831113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999135781/5000000000 : ℝ)^4641 ≤ (30843192739327/100000000000000 : ℝ)^3617 := by
    have hnat : (1999135781 : ℕ)^4641*100000000000000^3617 ≤ 30843192739327^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999135781 5000000000 30843192739327 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4370830339/10000000000 : ℝ)^4641 ≤ (34578399691169/100000000000000 : ℝ)^3617 := by
    have hnat : (4370830339 : ℕ)^4641*100000000000000^3617 ≤ 34578399691169^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370830339 10000000000 34578399691169 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4370831113/10000000000 : ℝ)^4641 ≤ (8644601886989/25000000000000 : ℝ)^3617 := by
    have hnat : (4370831113 : ℕ)^4641*25000000000000^3617 ≤ 8644601886989^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370831113 10000000000 8644601886989 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1999135781/5000000000 : ℝ), (4370830339/10000000000 : ℝ), (4370831113/10000000000 : ℝ)] ![(30843192739327/100000000000000 : ℝ), (34578399691169/100000000000000 : ℝ), (8644601886989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1999135781/5000000000 : ℝ)|^4641 ≤ (30843192739327/100000000000000 : ℝ)^3617
        have hw : |(1999135781/5000000000 : ℝ)|=(1999135781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4370830339/10000000000 : ℝ)|^4641 ≤ (34578399691169/100000000000000 : ℝ)^3617
        have hw : |(4370830339/10000000000 : ℝ)|=(4370830339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4370831113/10000000000 : ℝ)|^4641 ≤ (8644601886989/25000000000000 : ℝ)^3617
        have hw : |(4370831113/10000000000 : ℝ)|=(4370831113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1572_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(7979/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1841/3125 : ℝ) ∧ (4047/5000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86379/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1391/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1391/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1391/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1391/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1391/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1391/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (1391/12500 : ℝ) ^ (4639/1024 : ℝ) ≤ (299149865531609/6250000000000000000 : ℝ) := by
    have hpowers : (1391/12500 : ℝ)^4639 ≤ (299149865531609/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1391 : ℕ)^4639*6250000000000000000^1024 ≤ 299149865531609^1024*12500^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1391 12500 299149865531609 6250000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1391/12500 : ℝ)) (X := (299149865531609/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4639/1024 : ℝ) ≤ (5344280188499031/25000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4639 ≤ (5344280188499031/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4639*25000000000000000000^1024 ≤ 5344280188499031^1024*25000^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 5344280188499031 25000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (5344280188499031/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125299149865531609/3125000000000000000 : ℝ) ≤ (5000105649678737/5000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (3125299149865531609/3125000000000000000 : ℝ)^1024 ≤ (5000105649678737/5000000000000000 : ℝ)^4639 := by
      have hnat : (3125299149865531609 : ℕ)^1024*5000000000000000^4639 ≤ 5000105649678737^4639*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125299149865531609 3125000000000000000 5000105649678737 5000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000105649678737/5000000000000000 : ℝ)) (X := (3125299149865531609/3125000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006540879650625467/25000000000000000000 : ℝ) ≤ (5000288733696041/5000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (25006540879650625467/25000000000000000000 : ℝ)^1024 ≤ (5000288733696041/5000000000000000 : ℝ)^4639 := by
      have hnat : (25006540879650625467 : ℕ)^1024*5000000000000000^4639 ≤ 5000288733696041^4639*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006540879650625467 25000000000000000000 5000288733696041 5000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000288733696041/5000000000000000 : ℝ)) (X := (25006540879650625467/25000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505344280188499031/12500000000000000000 : ℝ) ≤ (1000094363542669/1000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (12505344280188499031/12500000000000000000 : ℝ)^1024 ≤ (1000094363542669/1000000000000000 : ℝ)^4639 := by
      have hnat : (12505344280188499031 : ℕ)^1024*1000000000000000^4639 ≤ 1000094363542669^4639*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505344280188499031 12500000000000000000 1000094363542669 1000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000094363542669/1000000000000000 : ℝ)) (X := (12505344280188499031/12500000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(299149865531609/6250000000000000000 : ℝ) ≤ ((1814698791009288379/1815000000000000000 : ℝ)+2*(7628500721/9075000000000 : ℝ)*(1391/12500 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (1814698791009288379/1815000000000000000 : ℝ)+2*(7628500721/9075000000000 : ℝ)*(1391/12500 : ℝ)=(5000105649678737/5000000000000000 : ℝ) by norm_num, show 1+2*(299149865531609/6250000000000000000 : ℝ)=(3125299149865531609/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5344280188499031/25000000000000000000 : ℝ)+(299149865531609/6250000000000000000 : ℝ) ≤ ((1814698791009288379/1815000000000000000 : ℝ)+(7628500721/9075000000000 : ℝ)*((3871/25000 : ℝ)+(1391/12500 : ℝ)))^(4639/1024 : ℝ) := by
    rw [show (1814698791009288379/1815000000000000000 : ℝ)+(7628500721/9075000000000 : ℝ)*((3871/25000 : ℝ)+(1391/12500 : ℝ))=(5000288733696041/5000000000000000 : ℝ) by norm_num, show 1+(5344280188499031/25000000000000000000 : ℝ)+(299149865531609/6250000000000000000 : ℝ)=(25006540879650625467/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5344280188499031/25000000000000000000 : ℝ) ≤ ((1814698791009288379/1815000000000000000 : ℝ)+2*(7628500721/9075000000000 : ℝ)*(3871/25000 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (1814698791009288379/1815000000000000000 : ℝ)+2*(7628500721/9075000000000 : ℝ)*(3871/25000 : ℝ)=(1000094363542669/1000000000000000 : ℝ) by norm_num, show 1+2*(5344280188499031/25000000000000000000 : ℝ)=(12505344280188499031/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1814698791009288379/1815000000000000000 : ℝ)*(X 1 0+X 2 0)+(7628500721/9075000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (1814698791009288379/1815000000000000000 : ℝ)) (alpha := (7628500721/9075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1814698791009288379/1815000000000000000 : ℝ)*(X 0 1+X 2 1)+(7628500721/9075000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (1814698791009288379/1815000000000000000 : ℝ)) (alpha := (7628500721/9075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1814698791009288379/1815000000000000000 : ℝ)*(X 0 2+X 1 2)+(7628500721/9075000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (1814698791009288379/1815000000000000000 : ℝ)) (alpha := (7628500721/9075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1579403939/10000000000 : ℝ)*X 0 0+(1349094251/2500000000 : ℝ)*X 0 1+(1349094259/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271143337/10000000000 : ℝ)*X 1 0+(-438375503/2500000000 : ℝ)*X 1 1+(5396377783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((329446483/625000000 : ℝ)*X 2 0+(337273609/625000000 : ℝ)*X 2 1+(-1753501533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4443235421/10000000000 : ℝ)*X 0 0+(518618087/1250000000 : ℝ)*X 0 1+(103723639/250000000 : ℝ)*X 0 2+(4443235421/10000000000 : ℝ)*X 1 0+(518618087/1250000000 : ℝ)*X 1 1+(103723639/250000000 : ℝ)*X 1 2+(4443235421/10000000000 : ℝ)*X 2 0+(518618087/1250000000 : ℝ)*X 2 1+(103723639/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-995879437/5000000000 : ℝ)*X 0 0+(1311272631/2500000000 : ℝ)*X 0 1+(5245090397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5375996713/10000000000 : ℝ)*X 1 0+(-908369017/5000000000 : ℝ)*X 1 1+(2622545247/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5375996837/10000000000 : ℝ)*X 2 0+(524509049/1000000000 : ℝ)*X 2 1+(-181673787/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4039315953/10000000000 : ℝ)*X 0 0+(13596179/31250000 : ℝ)*X 0 1+(217538899/500000000 : ℝ)*X 0 2+(4039315953/10000000000 : ℝ)*X 1 0+(13596179/31250000 : ℝ)*X 1 1+(217538899/500000000 : ℝ)*X 1 2+(4039315953/10000000000 : ℝ)*X 2 0+(13596179/31250000 : ℝ)*X 2 1+(217538899/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-952172859/5000000000 : ℝ)*X 0 0+(5138481667/10000000000 : ℝ)*X 0 1+(5416640317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628548271/5000000000 : ℝ)*X 1 0+(-436200133/2500000000 : ℝ)*X 1 1+(84635011/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((131427407/250000000 : ℝ)*X 2 0+(67708009/125000000 : ℝ)*X 2 1+(-872400433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1124048537/2500000000 : ℝ)*X 0 0+(32975009/80000000 : ℝ)*X 0 1+(4121877003/10000000000 : ℝ)*X 0 2+(1124048537/2500000000 : ℝ)*X 1 0+(32975009/80000000 : ℝ)*X 1 1+(4121877003/10000000000 : ℝ)*X 1 2+(1124048537/2500000000 : ℝ)*X 2 0+(32975009/80000000 : ℝ)*X 2 1+(4121877003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-833235167/5000000000 : ℝ)*X 0 0+(1099948433/2000000000 : ℝ)*X 0 1+(2615020649/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5386428763/10000000000 : ℝ)*X 1 0+(-911429213/5000000000 : ℝ)*X 1 1+(653755109/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5386428387/10000000000 : ℝ)*X 2 0+(5230041439/10000000000 : ℝ)*X 2 1+(-1822858173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1999135781/5000000000 : ℝ)*X 0 0+(4370830339/10000000000 : ℝ)*X 0 1+(4370831113/10000000000 : ℝ)*X 0 2+(1999135781/5000000000 : ℝ)*X 1 0+(4370830339/10000000000 : ℝ)*X 1 1+(4370831113/10000000000 : ℝ)*X 1 2+(1999135781/5000000000 : ℝ)*X 2 0+(4370830339/10000000000 : ℝ)*X 2 1+(4370831113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7979/12500 : ℝ) ≤ (-39893540438665573562491886317/62500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66752057/100000000000000 : ℝ)*(upper0) + (5994271/25000000000000 : ℝ)*(lower2) + (3703447/50000000000000 : ℝ)*(upper4) + (11067793/12500000000000 : ℝ)*(upper5) + (1155330718274183/50000000000000 : ℝ)*(major0) + (1155330718274183/50000000000000 : ℝ)*(major1) + (1155330718274183/50000000000000 : ℝ)*(major2) + (436254649/50000000000000 : ℝ)*(sp2) + (2970804353/100000000000000 : ℝ)*(sp3) + (817187210547119/25000000000000 : ℝ)*(sp4) + (3268750690448259/100000000000000 : ℝ)*(sp5) + (1634374908969481/50000000000000 : ℝ)*(sp6) + (343461441686183/25000000000000 : ℝ)*(sp7) + (924129891/50000000000000 : ℝ)*(sp8) + (686924368774543/50000000000000 : ℝ)*(f.failure) + (3268750690448259/100000000000000 : ℝ)*(f.sum) + (498412990519/165000000000000000000000000 : ℝ)*base65 + (109058982416974487/8250000000000000000000000000000 : ℝ)*base67 + (50035584686974487/8250000000000000000000000000000 : ℝ)*base69 + (72964397434474487/8250000000000000000000000000000 : ℝ)*base71 + (130083084287/82500000000000000000000000 : ℝ)*base73 + (13098238526974487/8250000000000000000000000000000 : ℝ)*base75 + (85629191298724487/8250000000000000000000000000000 : ℝ)*base77 + (19615583443525513/8250000000000000000000000000000 : ℝ)*base80 + (384429641807/82500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (11655409/2500000000000000000000 : ℝ)*base89 + (11655409/2500000000000000000000 : ℝ)*base91 + (11655409/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (1841/3125 : ℝ) ≤ (4455415030819483149586878926601/7562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20216141/12500000000000 : ℝ)*(lower1) + (21821299/50000000000000 : ℝ)*(lower3) + (176194639/100000000000000 : ℝ)*(upper4) + (312479/625000000000 : ℝ)*(upper5) + (597755417485627/25000000000000 : ℝ)*(major0) + (597755417485627/25000000000000 : ℝ)*(major1) + (597755417485627/25000000000000 : ℝ)*(major2) + (835194167066773/25000000000000 : ℝ)*(sp0) + (133630719128481/4000000000000 : ℝ)*(sp1) + (835190908021007/25000000000000 : ℝ)*(sp2) + (355396708945211/25000000000000 : ℝ)*(sp3) + (8690055067/100000000000000 : ℝ)*(sp5) + (1629522883/12500000000000 : ℝ)*(sp6) + (8328572753/20000000000000 : ℝ)*(sp11) + (142162847864461/10000000000000 : ℝ)*(f.failure) + (835194167066773/25000000000000 : ℝ)*(f.sum) + (794692598767/453750000000000000000000000 : ℝ)*base66 + (185405780472653633/45375000000000000000000000000000 : ℝ)*base67 + (73076254936403633/45375000000000000000000000000000 : ℝ)*base69 + (248328276566528633/45375000000000000000000000000000 : ℝ)*base71 + (529694976793/1815000000000000000000000000 : ℝ)*base74 + (125331268306028633/45375000000000000000000000000000 : ℝ)*base75 + (264430831513028633/45375000000000000000000000000000 : ℝ)*base77 + (361289180208653633/45375000000000000000000000000000 : ℝ)*base79 + (1651725907693/1815000000000000000000000000 : ℝ)*base82 + (4579443/500000000000000000000 : ℝ)*base89 + (4579443/500000000000000000000 : ℝ)*base91 + (4579443/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (4047/5000 : ℝ) ≤ (6121279498091021542624110468343/7562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1386329/50000000000000 : ℝ)*(upper0) + (88564897/100000000000000 : ℝ)*(lower1) + (3471269/2500000000000 : ℝ)*(upper2) + (6151317/12500000000000 : ℝ)*(lower5) + (644295587455961/25000000000000 : ℝ)*(major0) + (644295587455961/25000000000000 : ℝ)*(major1) + (644295587455961/25000000000000 : ℝ)*(major2) + (106866407/1562500000000 : ℝ)*(sp0) + (31793678243/100000000000000 : ℝ)*(sp1) + (6096598611/50000000000000 : ℝ)*(sp3) + (3595063079163473/100000000000000 : ℝ)*(sp8) + (1797519062467639/50000000000000 : ℝ)*(sp9) + (3595069918613521/100000000000000 : ℝ)*(sp10) + (1532301741564359/100000000000000 : ℝ)*(sp11) + (766156967380791/50000000000000 : ℝ)*(f.failure) + (3595069918613521/100000000000000 : ℝ)*(f.sum) + (362174205769/453750000000000000000000000 : ℝ)*base65 + (37269295136527219/45375000000000000000000000000000 : ℝ)*base67 + (87086507818027219/45375000000000000000000000000000 : ℝ)*base69 + (157268560507402219/45375000000000000000000000000000 : ℝ)*base71 + (33789340627529/1815000000000000000000000000 : ℝ)*base74 + (260682531661027219/45375000000000000000000000000000 : ℝ)*base75 + (123333672805027219/45375000000000000000000000000000 : ℝ)*base77 + (534092446932652219/45375000000000000000000000000000 : ℝ)*base79 + (8759902868131/1815000000000000000000000000 : ℝ)*base81 + (35660233/2500000000000000000000 : ℝ)*base89 + (35660233/2500000000000000000000 : ℝ)*base91 + (35660233/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-86379/100000 : ℝ) ≤ (-1187670662872674744734161573887/1375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4743479/25000000000000 : ℝ)*(lower1) + (3297739/5000000000000 : ℝ)*(lower3) + (54619669/100000000000000 : ℝ)*(lower4) + (2487419/3125000000000 : ℝ)*(upper5) + (2617721470878783/100000000000000 : ℝ)*(major0) + (2617721470878783/100000000000000 : ℝ)*(major1) + (2617721470878783/100000000000000 : ℝ)*(major2) + (1886304097/25000000000000 : ℝ)*(sp4) + (10160308481/12500000000000 : ℝ)*(sp5) + (2730049871/6250000000000 : ℝ)*(sp7) + (1853905077135973/50000000000000 : ℝ)*(sp12) + (1853868208510243/50000000000000 : ℝ)*(sp13) + (1853908849744167/50000000000000 : ℝ)*(sp14) + (1556373577540929/100000000000000 : ℝ)*(sp15) + (778208629169433/50000000000000 : ℝ)*(f.failure) + (1853908849744167/50000000000000 : ℝ)*(f.sum) + (824590566787/302500000000000000000000000 : ℝ)*base65 + (552263288216220919/60500000000000000000000000000000 : ℝ)*base67 + (450939353042220919/60500000000000000000000000000000 : ℝ)*base69 + (479336156548720919/60500000000000000000000000000000 : ℝ)*base71 + (678557785209/605000000000000000000000000 : ℝ)*base73 + (30525016937779081/60500000000000000000000000000000 : ℝ)*base76 + (255116210180720919/60500000000000000000000000000000 : ℝ)*base77 + (467807573664220919/60500000000000000000000000000000 : ℝ)*base79 + (2137438854349/605000000000000000000000000 : ℝ)*base81 + (29149479/2500000000000000000000 : ℝ)*base89 + (29149479/2500000000000000000000 : ℝ)*base91 + (29149479/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1572_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7979/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(1841/3125 : ℝ) else (4047/5000 : ℝ) ≤ X j i ∧ X j i ≤ (86379/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1572_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1572_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7979/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(1841/3125 : ℝ) else (4047/5000 : ℝ) ≤ X j i ∧ X j i ≤ (86379/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1572_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1572_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7979/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(1841/3125 : ℝ) else (4047/5000 : ℝ) ≤ X j i ∧ X j i ≤ (86379/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1572_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

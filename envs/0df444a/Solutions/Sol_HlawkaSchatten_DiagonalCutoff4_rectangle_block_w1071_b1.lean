-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1071_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:10:58.769422+00:00
-- url     : https://prove2.me/submissions/8271850c-f34f-43ea-a1c6-6e4ee24b955a

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
theorem support_rectangle_w1071_s3_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098319897/5000000000 : ℝ)*x 0 + (679618581/1250000000 : ℝ)*x 1 + (5224918369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098319897/5000000000 : ℝ)^1033 ≤ (333293320101/2500000000000 : ℝ)^777 := by
    have hnat : (1098319897 : ℕ)^1033*2500000000000^777 ≤ 333293320101^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098319897 5000000000 333293320101 2500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679618581/1250000000 : ℝ)^1033 ≤ (44479725932211/100000000000000 : ℝ)^777 := by
    have hnat : (679618581 : ℕ)^1033*100000000000000^777 ≤ 44479725932211^777*1250000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679618581 1250000000 44479725932211 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224918369/10000000000 : ℝ)^1033 ≤ (21094270621731/50000000000000 : ℝ)^777 := by
    have hnat : (5224918369 : ℕ)^1033*50000000000000^777 ≤ 21094270621731^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224918369 10000000000 21094270621731 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098319897/5000000000 : ℝ), (679618581/1250000000 : ℝ), (5224918369/10000000000 : ℝ)] ![(333293320101/2500000000000 : ℝ), (44479725932211/100000000000000 : ℝ), (21094270621731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098319897/5000000000 : ℝ)|^1033 ≤ (333293320101/2500000000000 : ℝ)^777
        have hw : |(-1098319897/5000000000 : ℝ)|=(1098319897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679618581/1250000000 : ℝ)|^1033 ≤ (44479725932211/100000000000000 : ℝ)^777
        have hw : |(679618581/1250000000 : ℝ)|=(679618581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224918369/10000000000 : ℝ)|^1033 ≤ (21094270621731/50000000000000 : ℝ)^777
        have hw : |(5224918369/10000000000 : ℝ)|=(5224918369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s3_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2677780243/5000000000 : ℝ)*x 0 + (-2305202631/10000000000 : ℝ)*x 1 + (5224918309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677780243/5000000000 : ℝ)^1033 ≤ (8719340795047/20000000000000 : ℝ)^777 := by
    have hnat : (2677780243 : ℕ)^1033*20000000000000^777 ≤ 8719340795047^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677780243 5000000000 8719340795047 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2305202631/10000000000 : ℝ)^1033 ≤ (3553688853251/25000000000000 : ℝ)^777 := by
    have hnat : (2305202631 : ℕ)^1033*25000000000000^777 ≤ 3553688853251^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305202631 10000000000 3553688853251 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224918309/10000000000 : ℝ)^1033 ≤ (21094270299687/50000000000000 : ℝ)^777 := by
    have hnat : (5224918309 : ℕ)^1033*50000000000000^777 ≤ 21094270299687^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224918309 10000000000 21094270299687 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677780243/5000000000 : ℝ), (-2305202631/10000000000 : ℝ), (5224918309/10000000000 : ℝ)] ![(8719340795047/20000000000000 : ℝ), (3553688853251/25000000000000 : ℝ), (21094270299687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677780243/5000000000 : ℝ)|^1033 ≤ (8719340795047/20000000000000 : ℝ)^777
        have hw : |(2677780243/5000000000 : ℝ)|=(2677780243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2305202631/10000000000 : ℝ)|^1033 ≤ (3553688853251/25000000000000 : ℝ)^777
        have hw : |(-2305202631/10000000000 : ℝ)|=(2305202631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224918309/10000000000 : ℝ)|^1033 ≤ (21094270299687/50000000000000 : ℝ)^777
        have hw : |(5224918309/10000000000 : ℝ)|=(5224918309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s3_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5355560429/10000000000 : ℝ)*x 0 + (261245907/500000000 : ℝ)*x 1 + (-2305202927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355560429/10000000000 : ℝ)^1033 ≤ (2724793959897/6250000000000 : ℝ)^777 := by
    have hnat : (5355560429 : ℕ)^1033*6250000000000^777 ≤ 2724793959897^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355560429 10000000000 2724793959897 6250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261245907/500000000 : ℝ)^1033 ≤ (42188538785191/100000000000000 : ℝ)^777 := by
    have hnat : (261245907 : ℕ)^1033*100000000000000^777 ≤ 42188538785191^777*500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261245907 500000000 42188538785191 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2305202927/10000000000 : ℝ)^1033 ≤ (14214757839621/100000000000000 : ℝ)^777 := by
    have hnat : (2305202927 : ℕ)^1033*100000000000000^777 ≤ 14214757839621^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305202927 10000000000 14214757839621 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355560429/10000000000 : ℝ), (261245907/500000000 : ℝ), (-2305202927/10000000000 : ℝ)] ![(2724793959897/6250000000000 : ℝ), (42188538785191/100000000000000 : ℝ), (14214757839621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355560429/10000000000 : ℝ)|^1033 ≤ (2724793959897/6250000000000 : ℝ)^777
        have hw : |(5355560429/10000000000 : ℝ)|=(5355560429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261245907/500000000 : ℝ)|^1033 ≤ (42188538785191/100000000000000 : ℝ)^777
        have hw : |(261245907/500000000 : ℝ)|=(261245907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2305202927/10000000000 : ℝ)|^1033 ≤ (14214757839621/100000000000000 : ℝ)^777
        have hw : |(-2305202927/10000000000 : ℝ)|=(2305202927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s3_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1093002609/2500000000 : ℝ)*x 0 + (4169026999/10000000000 : ℝ)*x 1 + (4584990213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093002609/2500000000 : ℝ)^1033 ≤ (33288604131927/100000000000000 : ℝ)^777 := by
    have hnat : (1093002609 : ℕ)^1033*100000000000000^777 ≤ 33288604131927^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093002609 2500000000 33288604131927 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169026999/10000000000 : ℝ)^1033 ≤ (390621974273/1250000000000 : ℝ)^777 := by
    have hnat : (4169026999 : ℕ)^1033*1250000000000^777 ≤ 390621974273^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169026999 10000000000 390621974273 1250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4584990213/10000000000 : ℝ)^1033 ≤ (35461637907951/100000000000000 : ℝ)^777 := by
    have hnat : (4584990213 : ℕ)^1033*100000000000000^777 ≤ 35461637907951^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584990213 10000000000 35461637907951 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093002609/2500000000 : ℝ), (4169026999/10000000000 : ℝ), (4584990213/10000000000 : ℝ)] ![(33288604131927/100000000000000 : ℝ), (390621974273/1250000000000 : ℝ), (35461637907951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093002609/2500000000 : ℝ)|^1033 ≤ (33288604131927/100000000000000 : ℝ)^777
        have hw : |(1093002609/2500000000 : ℝ)|=(1093002609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169026999/10000000000 : ℝ)|^1033 ≤ (390621974273/1250000000000 : ℝ)^777
        have hw : |(4169026999/10000000000 : ℝ)|=(4169026999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4584990213/10000000000 : ℝ)|^1033 ≤ (35461637907951/100000000000000 : ℝ)^777
        have hw : |(4584990213/10000000000 : ℝ)|=(4584990213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s3_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2196661851/10000000000 : ℝ)*x 0 + (2612892177/5000000000 : ℝ)*x 1 + (543607753/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2196661851/10000000000 : ℝ)^1033 ≤ (333297769427/2500000000000 : ℝ)^777 := by
    have hnat : (2196661851 : ℕ)^1033*2500000000000^777 ≤ 333297769427^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196661851 10000000000 333297769427 2500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612892177/5000000000 : ℝ)^1033 ≤ (1687913507217/4000000000000 : ℝ)^777 := by
    have hnat : (2612892177 : ℕ)^1033*4000000000000^777 ≤ 1687913507217^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612892177 5000000000 1687913507217 4000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543607753/1000000000 : ℝ)^1033 ≤ (222351257663/500000000000 : ℝ)^777 := by
    have hnat : (543607753 : ℕ)^1033*500000000000^777 ≤ 222351257663^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543607753 1000000000 222351257663 500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2196661851/10000000000 : ℝ), (2612892177/5000000000 : ℝ), (543607753/1000000000 : ℝ)] ![(333297769427/2500000000000 : ℝ), (1687913507217/4000000000000 : ℝ), (222351257663/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2196661851/10000000000 : ℝ)|^1033 ≤ (333297769427/2500000000000 : ℝ)^777
        have hw : |(-2196661851/10000000000 : ℝ)|=(2196661851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612892177/5000000000 : ℝ)|^1033 ≤ (1687913507217/4000000000000 : ℝ)^777
        have hw : |(2612892177/5000000000 : ℝ)|=(2612892177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543607753/1000000000 : ℝ)|^1033 ≤ (222351257663/500000000000 : ℝ)^777
        have hw : |(543607753/1000000000 : ℝ)|=(543607753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s3_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (106042603/200000000 : ℝ)*x 0 + (-130877637/625000000 : ℝ)*x 1 + (5436078273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106042603/200000000 : ℝ)^1033 ≤ (43019406070347/100000000000000 : ℝ)^777 := by
    have hnat : (106042603 : ℕ)^1033*100000000000000^777 ≤ 43019406070347^777*200000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106042603 200000000 43019406070347 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130877637/625000000 : ℝ)^1033 ≤ (12510334299897/100000000000000 : ℝ)^777 := by
    have hnat : (130877637 : ℕ)^1033*100000000000000^777 ≤ 12510334299897^777*625000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130877637 625000000 12510334299897 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436078273/10000000000 : ℝ)^1033 ≤ (44470259613357/100000000000000 : ℝ)^777 := by
    have hnat : (5436078273 : ℕ)^1033*100000000000000^777 ≤ 44470259613357^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436078273 10000000000 44470259613357 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106042603/200000000 : ℝ), (-130877637/625000000 : ℝ), (5436078273/10000000000 : ℝ)] ![(43019406070347/100000000000000 : ℝ), (12510334299897/100000000000000 : ℝ), (44470259613357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106042603/200000000 : ℝ)|^1033 ≤ (43019406070347/100000000000000 : ℝ)^777
        have hw : |(106042603/200000000 : ℝ)|=(106042603/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130877637/625000000 : ℝ)|^1033 ≤ (12510334299897/100000000000000 : ℝ)^777
        have hw : |(-130877637/625000000 : ℝ)|=(130877637/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436078273/10000000000 : ℝ)|^1033 ≤ (44470259613357/100000000000000 : ℝ)^777
        have hw : |(5436078273/10000000000 : ℝ)|=(5436078273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s3_6 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (42417037/80000000 : ℝ)*x 0 + (5436078177/10000000000 : ℝ)*x 1 + (-2094043037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42417037/80000000 : ℝ)^1033 ≤ (10754850101817/25000000000000 : ℝ)^777 := by
    have hnat : (42417037 : ℕ)^1033*25000000000000^777 ≤ 10754850101817^777*80000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42417037 80000000 10754850101817 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436078177/10000000000 : ℝ)^1033 ≤ (1778810342771/4000000000000 : ℝ)^777 := by
    have hnat : (5436078177 : ℕ)^1033*4000000000000^777 ≤ 1778810342771^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436078177 10000000000 1778810342771 4000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2094043037/10000000000 : ℝ)^1033 ≤ (3127585252849/25000000000000 : ℝ)^777 := by
    have hnat : (2094043037 : ℕ)^1033*25000000000000^777 ≤ 3127585252849^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094043037 10000000000 3127585252849 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42417037/80000000 : ℝ), (5436078177/10000000000 : ℝ), (-2094043037/10000000000 : ℝ)] ![(10754850101817/25000000000000 : ℝ), (1778810342771/4000000000000 : ℝ), (3127585252849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42417037/80000000 : ℝ)|^1033 ≤ (10754850101817/25000000000000 : ℝ)^777
        have hw : |(42417037/80000000 : ℝ)|=(42417037/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436078177/10000000000 : ℝ)|^1033 ≤ (1778810342771/4000000000000 : ℝ)^777
        have hw : |(5436078177/10000000000 : ℝ)|=(5436078177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2094043037/10000000000 : ℝ)|^1033 ≤ (3127585252849/25000000000000 : ℝ)^777
        have hw : |(-2094043037/10000000000 : ℝ)|=(2094043037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s3_7 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4372053627/10000000000 : ℝ)*x 0 + (916658387/2000000000 : ℝ)*x 1 + (4170735239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372053627/10000000000 : ℝ)^1033 ≤ (33289041339487/100000000000000 : ℝ)^777 := by
    have hnat : (4372053627 : ℕ)^1033*100000000000000^777 ≤ 33289041339487^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372053627 10000000000 33289041339487 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916658387/2000000000 : ℝ)^1033 ≤ (4430522048917/12500000000000 : ℝ)^777 := by
    have hnat : (916658387 : ℕ)^1033*12500000000000^777 ≤ 4430522048917^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916658387 2000000000 4430522048917 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170735239/10000000000 : ℝ)^1033 ≤ (31266782249177/100000000000000 : ℝ)^777 := by
    have hnat : (4170735239 : ℕ)^1033*100000000000000^777 ≤ 31266782249177^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170735239 10000000000 31266782249177 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372053627/10000000000 : ℝ), (916658387/2000000000 : ℝ), (4170735239/10000000000 : ℝ)] ![(33289041339487/100000000000000 : ℝ), (4430522048917/12500000000000 : ℝ), (31266782249177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372053627/10000000000 : ℝ)|^1033 ≤ (33289041339487/100000000000000 : ℝ)^777
        have hw : |(4372053627/10000000000 : ℝ)|=(4372053627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916658387/2000000000 : ℝ)|^1033 ≤ (4430522048917/12500000000000 : ℝ)^777
        have hw : |(916658387/2000000000 : ℝ)|=(916658387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170735239/10000000000 : ℝ)|^1033 ≤ (31266782249177/100000000000000 : ℝ)^777
        have hw : |(4170735239/10000000000 : ℝ)|=(4170735239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4181/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10413/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14899/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4181/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (273/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4181/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (273/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4181/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (273/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4181/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (273/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4181/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (273/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4181/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (273/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (273/3125 : ℝ) ^ (8263/2048 : ℝ) ≤ (5352392588066851/100000000000000000000 : ℝ) := by
    have hpowers : (273/3125 : ℝ)^8263 ≤ (5352392588066851/100000000000000000000 : ℝ)^2048 := by
      have hnat : (273 : ℕ)^8263*100000000000000000000^2048 ≤ 5352392588066851^2048*3125^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        273 3125 5352392588066851 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (273/3125 : ℝ)) (X := (5352392588066851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4181/25000 : ℝ) ^ (8263/2048 : ℝ) ≤ (4595316555027923/6250000000000000000 : ℝ) := by
    have hpowers : (4181/25000 : ℝ)^8263 ≤ (4595316555027923/6250000000000000000 : ℝ)^2048 := by
      have hnat : (4181 : ℕ)^8263*6250000000000000000^2048 ≤ 4595316555027923^2048*25000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4181 25000 4595316555027923 6250000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4181/25000 : ℝ)) (X := (4595316555027923/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005352392588066851/50000000000000000000 : ℝ) ≤ (10000265309421583/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50005352392588066851/50000000000000000000 : ℝ)^2048 ≤ (10000265309421583/10000000000000000 : ℝ)^8263 := by
      have hnat : (50005352392588066851 : ℕ)^2048*10000000000000000^8263 ≤ 10000265309421583^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005352392588066851 50000000000000000000 10000265309421583 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000265309421583/10000000000000000 : ℝ)) (X := (50005352392588066851/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100078877457468513619/100000000000000000000 : ℝ) ≤ (125024430160929/125000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (100078877457468513619/100000000000000000000 : ℝ)^2048 ≤ (125024430160929/125000000000000 : ℝ)^8263 := by
      have hnat : (100078877457468513619 : ℕ)^2048*125000000000000^8263 ≤ 125024430160929^8263*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100078877457468513619 100000000000000000000 125024430160929 125000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125024430160929/125000000000000 : ℝ)) (X := (100078877457468513619/100000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3129595316555027923/3125000000000000000 : ℝ) ≤ (10003643516327057/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (3129595316555027923/3125000000000000000 : ℝ)^2048 ≤ (10003643516327057/10000000000000000 : ℝ)^8263 := by
      have hnat : (3129595316555027923 : ℕ)^2048*10000000000000000^8263 ≤ 10003643516327057^8263*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3129595316555027923 3125000000000000000 10003643516327057 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003643516327057/10000000000000000 : ℝ)) (X := (3129595316555027923/3125000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5352392588066851/100000000000000000000 : ℝ) ≤ ((3992630363806669207/3994000000000000000 : ℝ)+2*(1689103452737/798800000000000 : ℝ)*(273/3125 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (3992630363806669207/3994000000000000000 : ℝ)+2*(1689103452737/798800000000000 : ℝ)*(273/3125 : ℝ)=(10000265309421583/10000000000000000 : ℝ) by norm_num, show 1+2*(5352392588066851/100000000000000000000 : ℝ)=(50005352392588066851/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4595316555027923/6250000000000000000 : ℝ)+(5352392588066851/100000000000000000000 : ℝ) ≤ ((3992630363806669207/3994000000000000000 : ℝ)+(1689103452737/798800000000000 : ℝ)*((4181/25000 : ℝ)+(273/3125 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (3992630363806669207/3994000000000000000 : ℝ)+(1689103452737/798800000000000 : ℝ)*((4181/25000 : ℝ)+(273/3125 : ℝ))=(125024430160929/125000000000000 : ℝ) by norm_num, show 1+(4595316555027923/6250000000000000000 : ℝ)+(5352392588066851/100000000000000000000 : ℝ)=(100078877457468513619/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4595316555027923/6250000000000000000 : ℝ) ≤ ((3992630363806669207/3994000000000000000 : ℝ)+2*(1689103452737/798800000000000 : ℝ)*(4181/25000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (3992630363806669207/3994000000000000000 : ℝ)+2*(1689103452737/798800000000000 : ℝ)*(4181/25000 : ℝ)=(10003643516327057/10000000000000000 : ℝ) by norm_num, show 1+2*(4595316555027923/6250000000000000000 : ℝ)=(3129595316555027923/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3992630363806669207/3994000000000000000 : ℝ)*(X 1 0+X 2 0)+(1689103452737/798800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (273/3125 : ℝ)) (hi := (4181/25000 : ℝ)) (c := (3992630363806669207/3994000000000000000 : ℝ)) (alpha := (1689103452737/798800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3992630363806669207/3994000000000000000 : ℝ)*(X 0 1+X 2 1)+(1689103452737/798800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (273/3125 : ℝ)) (hi := (4181/25000 : ℝ)) (c := (3992630363806669207/3994000000000000000 : ℝ)) (alpha := (1689103452737/798800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3992630363806669207/3994000000000000000 : ℝ)*(X 0 2+X 1 2)+(1689103452737/798800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (273/3125 : ℝ)) (hi := (4181/25000 : ℝ)) (c := (3992630363806669207/3994000000000000000 : ℝ)) (alpha := (1689103452737/798800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1098319897/5000000000 : ℝ)*X 0 0+(679618581/1250000000 : ℝ)*X 0 1+(5224918369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677780243/5000000000 : ℝ)*X 1 0+(-2305202631/10000000000 : ℝ)*X 1 1+(5224918309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355560429/10000000000 : ℝ)*X 2 0+(261245907/500000000 : ℝ)*X 2 1+(-2305202927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093002609/2500000000 : ℝ)*X 0 0+(4169026999/10000000000 : ℝ)*X 0 1+(4584990213/10000000000 : ℝ)*X 0 2+(1093002609/2500000000 : ℝ)*X 1 0+(4169026999/10000000000 : ℝ)*X 1 1+(4584990213/10000000000 : ℝ)*X 1 2+(1093002609/2500000000 : ℝ)*X 2 0+(4169026999/10000000000 : ℝ)*X 2 1+(4584990213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2196661851/10000000000 : ℝ)*X 0 0+(2612892177/5000000000 : ℝ)*X 0 1+(543607753/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106042603/200000000 : ℝ)*X 1 0+(-130877637/625000000 : ℝ)*X 1 1+(5436078273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42417037/80000000 : ℝ)*X 2 0+(5436078177/10000000000 : ℝ)*X 2 1+(-2094043037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372053627/10000000000 : ℝ)*X 0 0+(916658387/2000000000 : ℝ)*X 0 1+(4170735239/10000000000 : ℝ)*X 0 2+(4372053627/10000000000 : ℝ)*X 1 0+(916658387/2000000000 : ℝ)*X 1 1+(4170735239/10000000000 : ℝ)*X 1 2+(4372053627/10000000000 : ℝ)*X 2 0+(916658387/2000000000 : ℝ)*X 2 1+(4170735239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8934228285843019411136877/3994000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (404993003/100000000000000 : ℝ)*(base19) + (41407591/10000000000000 : ℝ)*(base23) + (46025533/100000000000000 : ℝ)*(upper2) + (129352921/100000000000000 : ℝ)*(upper3) + (71203843943021/2000000000000 : ℝ)*(major0) + (71203843943021/2000000000000 : ℝ)*(major1) + (71203843943021/2000000000000 : ℝ)*(major2) + (4716314409132337/100000000000000 : ℝ)*(sp0) + (2358157848271393/50000000000000 : ℝ)*(sp1) + (1179078253798613/25000000000000 : ℝ)*(sp2) + (601015719208023/25000000000000 : ℝ)*(sp3) + (1692403453/100000000000000 : ℝ)*(sp4) + (2672265427/100000000000000 : ℝ)*(sp6) + (2670685231/50000000000000 : ℝ)*(sp7) + (1202034109101277/50000000000000 : ℝ)*(f.failure) + (4716316101535789/100000000000000 : ℝ)*(f.sum) + (2804215479723/798800000000000000000000000 : ℝ)*base65 + (36177996035031347/7988000000000000000000000000000 : ℝ)*base67 + (57551848365123347/7988000000000000000000000000000 : ℝ)*base69 + (27843706921023347/7988000000000000000000000000000 : ℝ)*base71 + (7422381920143/3994000000000000000000000000 : ℝ)*base74 + (64881961230295347/7988000000000000000000000000000 : ℝ)*base75 + (125923879354467347/7988000000000000000000000000000 : ℝ)*base77 + (76914869960483347/7988000000000000000000000000000 : ℝ)*base79 + (14730429747651/3994000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4433549/1000000000000000000000 : ℝ)*base90 + (4433549/1000000000000000000000 : ℝ)*base92 + (4433549/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (471569898915911929551479943/49925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2505976751/100000000000000 : ℝ)*(base19) + (244702219/12500000000000 : ℝ)*(base23) + (13304319/100000000000000 : ℝ)*(upper2) + (115513579/25000000000000 : ℝ)*(upper3) + (897395183191839/25000000000000 : ℝ)*(major0) + (897395183191839/25000000000000 : ℝ)*(major1) + (897395183191839/25000000000000 : ℝ)*(major2) + (49013494829/100000000000000 : ℝ)*(sp1) + (38831488471/100000000000000 : ℝ)*(sp2) + (33882249/100000000000000 : ℝ)*(sp3) + (237762396198427/5000000000000 : ℝ)*(sp4) + (14859988764053/312500000000 : ℝ)*(sp5) + (1188801783715579/25000000000000 : ℝ)*(sp6) + (2423913192831703/100000000000000 : ℝ)*(sp7) + (75747288334811/3125000000000 : ℝ)*(f.failure) + (237762396198427/5000000000000 : ℝ)*(f.sum) + (14771658319791/4992500000000000000000000000 : ℝ)*base66 + (614554260844116673/99850000000000000000000000000000 : ℝ)*base67 + (325734337749816673/99850000000000000000000000000000 : ℝ)*base69 + (5900710397566673/99850000000000000000000000000000 : ℝ)*base71 + (12358061806449/4992500000000000000000000000 : ℝ)*base73 + (1808649818855966673/99850000000000000000000000000000 : ℝ)*base75 + (1377844237097316673/99850000000000000000000000000000 : ℝ)*base77 + (1681369762450916673/99850000000000000000000000000000 : ℝ)*base79 + (1774770052259/4992500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (208907/62500000000000000000 : ℝ)*base90 + (208907/62500000000000000000 : ℝ)*base92 + (208907/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1071_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4181/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14899/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1071_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1071_s4_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-550065883/2500000000 : ℝ)*x 0 + (5405539353/10000000000 : ℝ)*x 1 + (1050792127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550065883/2500000000 : ℝ)^1033 ≤ (6680489918401/50000000000000 : ℝ)^777 := by
    have hnat : (550065883 : ℕ)^1033*50000000000000^777 ≤ 6680489918401^777*2500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550065883 2500000000 6680489918401 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405539353/10000000000 : ℝ)^1033 ≤ (2206921531117/5000000000000 : ℝ)^777 := by
    have hnat : (5405539353 : ℕ)^1033*5000000000000^777 ≤ 2206921531117^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405539353 10000000000 2206921531117 5000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050792127/2000000000 : ℝ)^1033 ≤ (21250294763407/50000000000000 : ℝ)^777 := by
    have hnat : (1050792127 : ℕ)^1033*50000000000000^777 ≤ 21250294763407^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050792127 2000000000 21250294763407 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550065883/2500000000 : ℝ), (5405539353/10000000000 : ℝ), (1050792127/2000000000 : ℝ)] ![(6680489918401/50000000000000 : ℝ), (2206921531117/5000000000000 : ℝ), (21250294763407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550065883/2500000000 : ℝ)|^1033 ≤ (6680489918401/50000000000000 : ℝ)^777
        have hw : |(-550065883/2500000000 : ℝ)|=(550065883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405539353/10000000000 : ℝ)|^1033 ≤ (2206921531117/5000000000000 : ℝ)^777
        have hw : |(5405539353/10000000000 : ℝ)|=(5405539353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050792127/2000000000 : ℝ)|^1033 ≤ (21250294763407/50000000000000 : ℝ)^777
        have hw : |(1050792127/2000000000 : ℝ)|=(1050792127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s4_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673888493/5000000000 : ℝ)*x 0 + (-2277356069/10000000000 : ℝ)*x 1 + (2626980289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673888493/5000000000 : ℝ)^1033 ≤ (43512487136367/100000000000000 : ℝ)^777 := by
    have hnat : (2673888493 : ℕ)^1033*100000000000000^777 ≤ 43512487136367^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673888493 5000000000 43512487136367 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2277356069/10000000000 : ℝ)^1033 ≤ (559476957609/4000000000000 : ℝ)^777 := by
    have hnat : (2277356069 : ℕ)^1033*4000000000000^777 ≤ 559476957609^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277356069 10000000000 559476957609 4000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626980289/5000000000 : ℝ)^1033 ≤ (10625147228453/25000000000000 : ℝ)^777 := by
    have hnat : (2626980289 : ℕ)^1033*25000000000000^777 ≤ 10625147228453^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626980289 5000000000 10625147228453 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673888493/5000000000 : ℝ), (-2277356069/10000000000 : ℝ), (2626980289/5000000000 : ℝ)] ![(43512487136367/100000000000000 : ℝ), (559476957609/4000000000000 : ℝ), (10625147228453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673888493/5000000000 : ℝ)|^1033 ≤ (43512487136367/100000000000000 : ℝ)^777
        have hw : |(2673888493/5000000000 : ℝ)|=(2673888493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2277356069/10000000000 : ℝ)|^1033 ≤ (559476957609/4000000000000 : ℝ)^777
        have hw : |(-2277356069/10000000000 : ℝ)|=(2277356069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626980289/5000000000 : ℝ)|^1033 ≤ (10625147228453/25000000000000 : ℝ)^777
        have hw : |(2626980289/5000000000 : ℝ)|=(2626980289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s4_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347777099/10000000000 : ℝ)*x 0 + (1050792109/2000000000 : ℝ)*x 1 + (-1138677981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347777099/10000000000 : ℝ)^1033 ≤ (1740499534349/4000000000000 : ℝ)^777 := by
    have hnat : (5347777099 : ℕ)^1033*4000000000000^777 ≤ 1740499534349^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347777099 10000000000 1740499534349 4000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050792109/2000000000 : ℝ)^1033 ≤ (10625147139729/25000000000000 : ℝ)^777 := by
    have hnat : (1050792109 : ℕ)^1033*25000000000000^777 ≤ 10625147139729^777*2000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050792109 2000000000 10625147139729 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138677981/5000000000 : ℝ)^1033 ≤ (13986923066541/100000000000000 : ℝ)^777 := by
    have hnat : (1138677981 : ℕ)^1033*100000000000000^777 ≤ 13986923066541^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138677981 5000000000 13986923066541 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347777099/10000000000 : ℝ), (1050792109/2000000000 : ℝ), (-1138677981/5000000000 : ℝ)] ![(1740499534349/4000000000000 : ℝ), (10625147139729/25000000000000 : ℝ), (13986923066541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347777099/10000000000 : ℝ)|^1033 ≤ (1740499534349/4000000000000 : ℝ)^777
        have hw : |(5347777099/10000000000 : ℝ)|=(5347777099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050792109/2000000000 : ℝ)|^1033 ≤ (10625147139729/25000000000000 : ℝ)^777
        have hw : |(1050792109/2000000000 : ℝ)|=(1050792109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1138677981/5000000000 : ℝ)|^1033 ≤ (13986923066541/100000000000000 : ℝ)^777
        have hw : |(-1138677981/5000000000 : ℝ)|=(1138677981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s4_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2187084851/5000000000 : ℝ)*x 0 + (4228041441/10000000000 : ℝ)*x 1 + (2262704779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187084851/5000000000 : ℝ)^1033 ≤ (33310463377687/100000000000000 : ℝ)^777 := by
    have hnat : (2187084851 : ℕ)^1033*100000000000000^777 ≤ 33310463377687^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187084851 5000000000 33310463377687 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228041441/10000000000 : ℝ)^1033 ≤ (31839222826089/100000000000000 : ℝ)^777 := by
    have hnat : (4228041441 : ℕ)^1033*100000000000000^777 ≤ 31839222826089^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228041441 10000000000 31839222826089 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262704779/5000000000 : ℝ)^1033 ≤ (4356289221533/12500000000000 : ℝ)^777 := by
    have hnat : (2262704779 : ℕ)^1033*12500000000000^777 ≤ 4356289221533^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262704779 5000000000 4356289221533 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187084851/5000000000 : ℝ), (4228041441/10000000000 : ℝ), (2262704779/5000000000 : ℝ)] ![(33310463377687/100000000000000 : ℝ), (31839222826089/100000000000000 : ℝ), (4356289221533/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187084851/5000000000 : ℝ)|^1033 ≤ (33310463377687/100000000000000 : ℝ)^777
        have hw : |(2187084851/5000000000 : ℝ)|=(2187084851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228041441/10000000000 : ℝ)|^1033 ≤ (31839222826089/100000000000000 : ℝ)^777
        have hw : |(4228041441/10000000000 : ℝ)|=(4228041441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262704779/5000000000 : ℝ)|^1033 ≤ (4356289221533/12500000000000 : ℝ)^777
        have hw : |(2262704779/5000000000 : ℝ)|=(2262704779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s4_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100135857/5000000000 : ℝ)*x 0 + (5254403897/10000000000 : ℝ)*x 1 + (337818383/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100135857/5000000000 : ℝ)^1033 ≤ (13361045891339/100000000000000 : ℝ)^777 := by
    have hnat : (1100135857 : ℕ)^1033*100000000000000^777 ≤ 13361045891339^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100135857 5000000000 13361045891339 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254403897/10000000000 : ℝ)^1033 ≤ (21252678311857/50000000000000 : ℝ)^777 := by
    have hnat : (5254403897 : ℕ)^1033*50000000000000^777 ≤ 21252678311857^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254403897 10000000000 21252678311857 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337818383/625000000 : ℝ)^1033 ≤ (22066798733207/50000000000000 : ℝ)^777 := by
    have hnat : (337818383 : ℕ)^1033*50000000000000^777 ≤ 22066798733207^777*625000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337818383 625000000 22066798733207 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100135857/5000000000 : ℝ), (5254403897/10000000000 : ℝ), (337818383/625000000 : ℝ)] ![(13361045891339/100000000000000 : ℝ), (21252678311857/50000000000000 : ℝ), (22066798733207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100135857/5000000000 : ℝ)|^1033 ≤ (13361045891339/100000000000000 : ℝ)^777
        have hw : |(-1100135857/5000000000 : ℝ)|=(1100135857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254403897/10000000000 : ℝ)|^1033 ≤ (21252678311857/50000000000000 : ℝ)^777
        have hw : |(5254403897/10000000000 : ℝ)|=(5254403897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337818383/625000000 : ℝ)|^1033 ≤ (22066798733207/50000000000000 : ℝ)^777
        have hw : |(337818383/625000000 : ℝ)|=(337818383/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s4_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (663698061/1250000000 : ℝ)*x 0 + (-2126222123/10000000000 : ℝ)*x 1 + (33781837/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663698061/1250000000 : ℝ)^1033 ≤ (430998332707/1000000000000 : ℝ)^777 := by
    have hnat : (663698061 : ℕ)^1033*1000000000000^777 ≤ 430998332707^777*1250000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663698061 1250000000 430998332707 1000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126222123/10000000000 : ℝ)^1033 ≤ (12766571517537/100000000000000 : ℝ)^777 := by
    have hnat : (2126222123 : ℕ)^1033*100000000000000^777 ≤ 12766571517537^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126222123 10000000000 12766571517537 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33781837/62500000 : ℝ)^1033 ≤ (44133595208493/100000000000000 : ℝ)^777 := by
    have hnat : (33781837 : ℕ)^1033*100000000000000^777 ≤ 44133595208493^777*62500000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33781837 62500000 44133595208493 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663698061/1250000000 : ℝ), (-2126222123/10000000000 : ℝ), (33781837/62500000 : ℝ)] ![(430998332707/1000000000000 : ℝ), (12766571517537/100000000000000 : ℝ), (44133595208493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663698061/1250000000 : ℝ)|^1033 ≤ (430998332707/1000000000000 : ℝ)^777
        have hw : |(663698061/1250000000 : ℝ)|=(663698061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126222123/10000000000 : ℝ)|^1033 ≤ (12766571517537/100000000000000 : ℝ)^777
        have hw : |(-2126222123/10000000000 : ℝ)|=(2126222123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33781837/62500000 : ℝ)|^1033 ≤ (44133595208493/100000000000000 : ℝ)^777
        have hw : |(33781837/62500000 : ℝ)|=(33781837/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s4_6 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5309584317/10000000000 : ℝ)*x 0 + (5405093931/10000000000 : ℝ)*x 1 + (-2126222337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309584317/10000000000 : ℝ)^1033 ≤ (430998314253/1000000000000 : ℝ)^777 := by
    have hnat : (5309584317 : ℕ)^1033*1000000000000^777 ≤ 430998314253^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309584317 10000000000 430998314253 1000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405093931/10000000000 : ℝ)^1033 ≤ (22066797663951/50000000000000 : ℝ)^777 := by
    have hnat : (5405093931 : ℕ)^1033*50000000000000^777 ≤ 22066797663951^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405093931 10000000000 22066797663951 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126222337/10000000000 : ℝ)^1033 ≤ (1595821653227/12500000000000 : ℝ)^777 := by
    have hnat : (2126222337 : ℕ)^1033*12500000000000^777 ≤ 1595821653227^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126222337 10000000000 1595821653227 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309584317/10000000000 : ℝ), (5405093931/10000000000 : ℝ), (-2126222337/10000000000 : ℝ)] ![(430998314253/1000000000000 : ℝ), (22066797663951/50000000000000 : ℝ), (1595821653227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309584317/10000000000 : ℝ)|^1033 ≤ (430998314253/1000000000000 : ℝ)^777
        have hw : |(5309584317/10000000000 : ℝ)|=(5309584317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405093931/10000000000 : ℝ)|^1033 ≤ (22066797663951/50000000000000 : ℝ)^777
        have hw : |(5405093931/10000000000 : ℝ)|=(5405093931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2126222337/10000000000 : ℝ)|^1033 ≤ (1595821653227/12500000000000 : ℝ)^777
        have hw : |(-2126222337/10000000000 : ℝ)|=(2126222337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s4_7 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4374185451/10000000000 : ℝ)*x 0 + (2262269887/5000000000 : ℝ)*x 1 + (4228914939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374185451/10000000000 : ℝ)^1033 ≤ (33310622825141/100000000000000 : ℝ)^777 := by
    have hnat : (4374185451 : ℕ)^1033*100000000000000^777 ≤ 33310622825141^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374185451 10000000000 33310622825141 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262269887/5000000000 : ℝ)^1033 ≤ (17420704469743/50000000000000 : ℝ)^777 := by
    have hnat : (2262269887 : ℕ)^1033*50000000000000^777 ≤ 17420704469743^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262269887 5000000000 17420704469743 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228914939/10000000000 : ℝ)^1033 ≤ (31847968216871/100000000000000 : ℝ)^777 := by
    have hnat : (4228914939 : ℕ)^1033*100000000000000^777 ≤ 31847968216871^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228914939 10000000000 31847968216871 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374185451/10000000000 : ℝ), (2262269887/5000000000 : ℝ), (4228914939/10000000000 : ℝ)] ![(33310622825141/100000000000000 : ℝ), (17420704469743/50000000000000 : ℝ), (31847968216871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374185451/10000000000 : ℝ)|^1033 ≤ (33310622825141/100000000000000 : ℝ)^777
        have hw : |(4374185451/10000000000 : ℝ)|=(4374185451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262269887/5000000000 : ℝ)|^1033 ≤ (17420704469743/50000000000000 : ℝ)^777
        have hw : |(2262269887/5000000000 : ℝ)|=(2262269887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228914939/10000000000 : ℝ)|^1033 ≤ (31847968216871/100000000000000 : ℝ)^777
        have hw : |(4228914939/10000000000 : ℝ)|=(4228914939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11033/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7121/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14899/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14899/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14899/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14899/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14899/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14899/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10413/100000 : ℝ) ^ (8263/2048 : ℝ) ≤ (2174076492198069/20000000000000000000 : ℝ) := by
    have hpowers : (10413/100000 : ℝ)^8263 ≤ (2174076492198069/20000000000000000000 : ℝ)^2048 := by
      have hnat : (10413 : ℕ)^8263*20000000000000000000^2048 ≤ 2174076492198069^2048*100000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10413 100000 2174076492198069 20000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10413/100000 : ℝ)) (X := (2174076492198069/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14899/100000 : ℝ) ^ (8263/2048 : ℝ) ≤ (46127882363234061/100000000000000000000 : ℝ) := by
    have hpowers : (14899/100000 : ℝ)^8263 ≤ (46127882363234061/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14899 : ℕ)^8263*100000000000000000000^2048 ≤ 46127882363234061^2048*100000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14899 100000 46127882363234061 100000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14899/100000 : ℝ)) (X := (46127882363234061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002174076492198069/10000000000000000000 : ℝ) ≤ (10000538804872201/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (10002174076492198069/10000000000000000000 : ℝ)^2048 ≤ (10000538804872201/10000000000000000 : ℝ)^8263 := by
      have hnat : (10002174076492198069 : ℕ)^2048*10000000000000000^8263 ≤ 10000538804872201^8263*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002174076492198069 10000000000000000000 10000538804872201 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538804872201/10000000000000000 : ℝ)) (X := (10002174076492198069/10000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028499132412112203/50000000000000000000 : ℝ) ≤ (2500353102482217/2500000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50028499132412112203/50000000000000000000 : ℝ)^2048 ≤ (2500353102482217/2500000000000000 : ℝ)^8263 := by
      have hnat : (50028499132412112203 : ℕ)^2048*2500000000000000^8263 ≤ 2500353102482217^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028499132412112203 50000000000000000000 2500353102482217 2500000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500353102482217/2500000000000000 : ℝ)) (X := (50028499132412112203/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50046127882363234061/50000000000000000000 : ℝ) ≤ (2000457202997107/2000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50046127882363234061/50000000000000000000 : ℝ)^2048 ≤ (2000457202997107/2000000000000000 : ℝ)^8263 := by
      have hnat : (50046127882363234061 : ℕ)^2048*2000000000000000^8263 ≤ 2000457202997107^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046127882363234061 50000000000000000000 2000457202997107 2000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000457202997107/2000000000000000 : ℝ)) (X := (50046127882363234061/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2174076492198069/20000000000000000000 : ℝ) ≤ ((5605527922468318343/5607500000000000000 : ℝ)+2*(873605056667/448600000000000 : ℝ)*(10413/100000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (5605527922468318343/5607500000000000000 : ℝ)+2*(873605056667/448600000000000 : ℝ)*(10413/100000 : ℝ)=(10000538804872201/10000000000000000 : ℝ) by norm_num, show 1+2*(2174076492198069/20000000000000000000 : ℝ)=(10002174076492198069/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46127882363234061/100000000000000000000 : ℝ)+(2174076492198069/20000000000000000000 : ℝ) ≤ ((5605527922468318343/5607500000000000000 : ℝ)+(873605056667/448600000000000 : ℝ)*((14899/100000 : ℝ)+(10413/100000 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (5605527922468318343/5607500000000000000 : ℝ)+(873605056667/448600000000000 : ℝ)*((14899/100000 : ℝ)+(10413/100000 : ℝ))=(2500353102482217/2500000000000000 : ℝ) by norm_num, show 1+(46127882363234061/100000000000000000000 : ℝ)+(2174076492198069/20000000000000000000 : ℝ)=(50028499132412112203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46127882363234061/100000000000000000000 : ℝ) ≤ ((5605527922468318343/5607500000000000000 : ℝ)+2*(873605056667/448600000000000 : ℝ)*(14899/100000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (5605527922468318343/5607500000000000000 : ℝ)+2*(873605056667/448600000000000 : ℝ)*(14899/100000 : ℝ)=(2000457202997107/2000000000000000 : ℝ) by norm_num, show 1+2*(46127882363234061/100000000000000000000 : ℝ)=(50046127882363234061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5605527922468318343/5607500000000000000 : ℝ)*(X 1 0+X 2 0)+(873605056667/448600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (10413/100000 : ℝ)) (hi := (14899/100000 : ℝ)) (c := (5605527922468318343/5607500000000000000 : ℝ)) (alpha := (873605056667/448600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5605527922468318343/5607500000000000000 : ℝ)*(X 0 1+X 2 1)+(873605056667/448600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (10413/100000 : ℝ)) (hi := (14899/100000 : ℝ)) (c := (5605527922468318343/5607500000000000000 : ℝ)) (alpha := (873605056667/448600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5605527922468318343/5607500000000000000 : ℝ)*(X 0 2+X 1 2)+(873605056667/448600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (10413/100000 : ℝ)) (hi := (14899/100000 : ℝ)) (c := (5605527922468318343/5607500000000000000 : ℝ)) (alpha := (873605056667/448600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-550065883/2500000000 : ℝ)*X 0 0+(5405539353/10000000000 : ℝ)*X 0 1+(1050792127/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673888493/5000000000 : ℝ)*X 1 0+(-2277356069/10000000000 : ℝ)*X 1 1+(2626980289/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347777099/10000000000 : ℝ)*X 2 0+(1050792109/2000000000 : ℝ)*X 2 1+(-1138677981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187084851/5000000000 : ℝ)*X 0 0+(4228041441/10000000000 : ℝ)*X 0 1+(2262704779/5000000000 : ℝ)*X 0 2+(2187084851/5000000000 : ℝ)*X 1 0+(4228041441/10000000000 : ℝ)*X 1 1+(2262704779/5000000000 : ℝ)*X 1 2+(2187084851/5000000000 : ℝ)*X 2 0+(4228041441/10000000000 : ℝ)*X 2 1+(2262704779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1100135857/5000000000 : ℝ)*X 0 0+(5254403897/10000000000 : ℝ)*X 0 1+(337818383/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663698061/1250000000 : ℝ)*X 1 0+(-2126222123/10000000000 : ℝ)*X 1 1+(33781837/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309584317/10000000000 : ℝ)*X 2 0+(5405093931/10000000000 : ℝ)*X 2 1+(-2126222337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4374185451/10000000000 : ℝ)*X 0 0+(2262269887/5000000000 : ℝ)*X 0 1+(4228914939/10000000000 : ℝ)*X 0 2+(4374185451/10000000000 : ℝ)*X 1 0+(2262269887/5000000000 : ℝ)*X 1 1+(4228914939/10000000000 : ℝ)*X 1 2+(4374185451/10000000000 : ℝ)*X 2 0+(2262269887/5000000000 : ℝ)*X 2 1+(4228914939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (154462818209228198191268253/35046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119962993/20000000000000 : ℝ)*(base19) + (196318741/50000000000000 : ℝ)*(base23) + (39719261/20000000000000 : ℝ)*(lower2) + (45469229/50000000000000 : ℝ)*(upper3) + (13253479/100000000000000 : ℝ)*(lower4) + (622506018461707/12500000000000 : ℝ)*(major0) + (622506018461707/12500000000000 : ℝ)*(major1) + (622506018461707/12500000000000 : ℝ)*(major2) + (6597240551547543/100000000000000 : ℝ)*(sp0) + (6597250282451193/100000000000000 : ℝ)*(sp1) + (1649312622407169/25000000000000 : ℝ)*(sp2) + (336283833855839/10000000000000 : ℝ)*(sp3) + (2066143723/20000000000000 : ℝ)*(sp4) + (1731913017/25000000000000 : ℝ)*(sp7) + (1681422633105229/50000000000000 : ℝ)*(f.failure) + (3298625441133079/50000000000000 : ℝ)*(f.sum) + (4563936169527/5607500000000000000000000000 : ℝ)*base66 + (170517030908820999/70093750000000000000000000000000 : ℝ)*base68 + (609002715938914749/70093750000000000000000000000000 : ℝ)*base70 + (692903964560866501/70093750000000000000000000000000 : ℝ)*base71 + (11550848898299/11215000000000000000000000000 : ℝ)*base74 + (610496205502883499/70093750000000000000000000000000 : ℝ)*base76 + (774357753630320999/70093750000000000000000000000000 : ℝ)*base78 + (25662331875616501/70093750000000000000000000000000 : ℝ)*base79 + (7118618231781/2803750000000000000000000000 : ℝ)*base82 + (1848573/1000000000000000000000 : ℝ)*base90 + (1848573/1000000000000000000000 : ℝ)*base92 + (1848573/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42754185731298276620781/22430000000000000000000000000 : ℝ) := by norm_num
    linear_combination (683606333/50000000000000 : ℝ)*(base19) + (1265397717/100000000000000 : ℝ)*(base23) + (92236133/100000000000000 : ℝ)*(lower4) + (27607067/50000000000000 : ℝ)*(upper5) + (5009395884833423/100000000000000 : ℝ)*(major0) + (5009395884833423/100000000000000 : ℝ)*(major1) + (5009395884833423/100000000000000 : ℝ)*(major2) + (532029689/100000000000000 : ℝ)*(sp0) + (16483147969/50000000000000 : ℝ)*(sp1) + (24373365489/100000000000000 : ℝ)*(sp2) + (6636128449104443/100000000000000 : ℝ)*(sp4) + (829511830953191/12500000000000 : ℝ)*(sp5) + (3318051671185463/50000000000000 : ℝ)*(sp6) + (1691331362497751/50000000000000 : ℝ)*(sp7) + (1691331362497751/50000000000000 : ℝ)*(f.failure) + (1659032245283533/25000000000000 : ℝ)*(f.sum) + (206808278179781/22430000000000000000000000000 : ℝ)*base65 + (3796007822007359411/560750000000000000000000000000000 : ℝ)*base68 + (5732863814263109411/560750000000000000000000000000000 : ℝ)*base70 + (5058811242264140589/560750000000000000000000000000000 : ℝ)*base71 + (45617812237881/22430000000000000000000000000 : ℝ)*base73 + (342833153091859411/560750000000000000000000000000000 : ℝ)*base76 + (845217187938390589/560750000000000000000000000000000 : ℝ)*base77 + (111849943095390589/560750000000000000000000000000000 : ℝ)*base79 + (124722993819001/22430000000000000000000000000 : ℝ)*base81 + (3523687/1000000000000000000000 : ℝ)*base90 + (3523687/1000000000000000000000 : ℝ)*base92 + (3523687/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1071_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1071_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1071_s5_0 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100540857/5000000000 : ℝ)*x 0 + (5396851637/10000000000 : ℝ)*x 1 + (5262111509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100540857/5000000000 : ℝ)^1033 ≤ (334189638643/2500000000000 : ℝ)^777 := by
    have hnat : (1100540857 : ℕ)^1033*2500000000000^777 ≤ 334189638643^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100540857 5000000000 334189638643 2500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396851637/10000000000 : ℝ)^1033 ≤ (22022072254789/50000000000000 : ℝ)^777 := by
    have hnat : (5396851637 : ℕ)^1033*50000000000000^777 ≤ 22022072254789^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396851637 10000000000 22022072254789 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262111509/10000000000 : ℝ)^1033 ≤ (10647067483659/25000000000000 : ℝ)^777 := by
    have hnat : (5262111509 : ℕ)^1033*25000000000000^777 ≤ 10647067483659^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262111509 10000000000 10647067483659 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100540857/5000000000 : ℝ), (5396851637/10000000000 : ℝ), (5262111509/10000000000 : ℝ)] ![(334189638643/2500000000000 : ℝ), (22022072254789/50000000000000 : ℝ), (10647067483659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100540857/5000000000 : ℝ)|^1033 ≤ (334189638643/2500000000000 : ℝ)^777
        have hw : |(-1100540857/5000000000 : ℝ)|=(1100540857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396851637/10000000000 : ℝ)|^1033 ≤ (22022072254789/50000000000000 : ℝ)^777
        have hw : |(5396851637/10000000000 : ℝ)|=(5396851637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262111509/10000000000 : ℝ)|^1033 ≤ (10647067483659/25000000000000 : ℝ)^777
        have hw : |(5262111509/10000000000 : ℝ)|=(5262111509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s5_1 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672805919/5000000000 : ℝ)*x 0 + (-2269481479/10000000000 : ℝ)*x 1 + (657763939/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672805919/5000000000 : ℝ)^1033 ≤ (21744533793309/50000000000000 : ℝ)^777 := by
    have hnat : (2672805919 : ℕ)^1033*50000000000000^777 ≤ 21744533793309^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672805919 5000000000 21744533793309 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269481479/10000000000 : ℝ)^1033 ≤ (6961331218319/50000000000000 : ℝ)^777 := by
    have hnat : (2269481479 : ℕ)^1033*50000000000000^777 ≤ 6961331218319^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269481479 10000000000 6961331218319 50000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657763939/1250000000 : ℝ)^1033 ≤ (10647067491729/25000000000000 : ℝ)^777 := by
    have hnat : (657763939 : ℕ)^1033*25000000000000^777 ≤ 10647067491729^777*1250000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657763939 1250000000 10647067491729 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672805919/5000000000 : ℝ), (-2269481479/10000000000 : ℝ), (657763939/1250000000 : ℝ)] ![(21744533793309/50000000000000 : ℝ), (6961331218319/50000000000000 : ℝ), (10647067491729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672805919/5000000000 : ℝ)|^1033 ≤ (21744533793309/50000000000000 : ℝ)^777
        have hw : |(2672805919/5000000000 : ℝ)|=(2672805919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2269481479/10000000000 : ℝ)|^1033 ≤ (6961331218319/50000000000000 : ℝ)^777
        have hw : |(-2269481479/10000000000 : ℝ)|=(2269481479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657763939/1250000000 : ℝ)|^1033 ≤ (10647067491729/25000000000000 : ℝ)^777
        have hw : |(657763939/1250000000 : ℝ)|=(657763939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s5_2 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (334100739/625000000 : ℝ)*x 0 + (526211151/1000000000 : ℝ)*x 1 + (-2269481499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334100739/625000000 : ℝ)^1033 ≤ (8697813487039/20000000000000 : ℝ)^777 := by
    have hnat : (334100739 : ℕ)^1033*20000000000000^777 ≤ 8697813487039^777*625000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334100739 625000000 8697813487039 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526211151/1000000000 : ℝ)^1033 ≤ (10647067486349/25000000000000 : ℝ)^777 := by
    have hnat : (526211151 : ℕ)^1033*25000000000000^777 ≤ 10647067486349^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526211151 1000000000 10647067486349 25000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269481499/10000000000 : ℝ)^1033 ≤ (13922662599757/100000000000000 : ℝ)^777 := by
    have hnat : (2269481499 : ℕ)^1033*100000000000000^777 ≤ 13922662599757^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269481499 10000000000 13922662599757 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334100739/625000000 : ℝ), (526211151/1000000000 : ℝ), (-2269481499/10000000000 : ℝ)] ![(8697813487039/20000000000000 : ℝ), (10647067486349/25000000000000 : ℝ), (13922662599757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334100739/625000000 : ℝ)|^1033 ≤ (8697813487039/20000000000000 : ℝ)^777
        have hw : |(334100739/625000000 : ℝ)|=(334100739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526211151/1000000000 : ℝ)|^1033 ≤ (10647067486349/25000000000000 : ℝ)^777
        have hw : |(526211151/1000000000 : ℝ)|=(526211151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2269481499/10000000000 : ℝ)|^1033 ≤ (13922662599757/100000000000000 : ℝ)^777
        have hw : |(-2269481499/10000000000 : ℝ)|=(2269481499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s5_3 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4374643293/10000000000 : ℝ)*x 0 + (2122248163/5000000000 : ℝ)*x 1 + (4508830423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374643293/10000000000 : ℝ)^1033 ≤ (6663051646663/20000000000000 : ℝ)^777 := by
    have hnat : (4374643293 : ℕ)^1033*20000000000000^777 ≤ 6663051646663^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374643293 10000000000 6663051646663 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122248163/5000000000 : ℝ)^1033 ≤ (32004067714359/100000000000000 : ℝ)^777 := by
    have hnat : (2122248163 : ℕ)^1033*100000000000000^777 ≤ 32004067714359^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122248163 5000000000 32004067714359 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508830423/10000000000 : ℝ)^1033 ≤ (2167542127629/6250000000000 : ℝ)^777 := by
    have hnat : (4508830423 : ℕ)^1033*6250000000000^777 ≤ 2167542127629^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508830423 10000000000 2167542127629 6250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374643293/10000000000 : ℝ), (2122248163/5000000000 : ℝ), (4508830423/10000000000 : ℝ)] ![(6663051646663/20000000000000 : ℝ), (32004067714359/100000000000000 : ℝ), (2167542127629/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374643293/10000000000 : ℝ)|^1033 ≤ (6663051646663/20000000000000 : ℝ)^777
        have hw : |(4374643293/10000000000 : ℝ)|=(4374643293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122248163/5000000000 : ℝ)|^1033 ≤ (32004067714359/100000000000000 : ℝ)^777
        have hw : |(2122248163/5000000000 : ℝ)|=(2122248163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508830423/10000000000 : ℝ)|^1033 ≤ (2167542127629/6250000000000 : ℝ)^777
        have hw : |(4508830423/10000000000 : ℝ)|=(4508830423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s5_4 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-110054369/500000000 : ℝ)*x 0 + (5262462023/10000000000 : ℝ)*x 1 + (2698249903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110054369/500000000 : ℝ)^1033 ≤ (13367631293799/100000000000000 : ℝ)^777 := by
    have hnat : (110054369 : ℕ)^1033*100000000000000^777 ≤ 13367631293799^777*500000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110054369 500000000 13367631293799 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262462023/10000000000 : ℝ)^1033 ≤ (5324005185057/12500000000000 : ℝ)^777 := by
    have hnat : (5262462023 : ℕ)^1033*12500000000000^777 ≤ 5324005185057^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262462023 10000000000 5324005185057 12500000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698249903/5000000000 : ℝ)^1033 ≤ (2752520450517/6250000000000 : ℝ)^777 := by
    have hnat : (2698249903 : ℕ)^1033*6250000000000^777 ≤ 2752520450517^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698249903 5000000000 2752520450517 6250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110054369/500000000 : ℝ), (5262462023/10000000000 : ℝ), (2698249903/5000000000 : ℝ)] ![(13367631293799/100000000000000 : ℝ), (5324005185057/12500000000000 : ℝ), (2752520450517/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110054369/500000000 : ℝ)|^1033 ≤ (13367631293799/100000000000000 : ℝ)^777
        have hw : |(-110054369/500000000 : ℝ)|=(110054369/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262462023/10000000000 : ℝ)|^1033 ≤ (5324005185057/12500000000000 : ℝ)^777
        have hw : |(5262462023/10000000000 : ℝ)|=(5262462023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698249903/5000000000 : ℝ)|^1033 ≤ (2752520450517/6250000000000 : ℝ)^777
        have hw : |(2698249903/5000000000 : ℝ)|=(2698249903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s5_5 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (531166047/1000000000 : ℝ)*x 0 + (-33360831/156250000 : ℝ)*x 1 + (5396499813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531166047/1000000000 : ℝ)^1033 ≤ (134756994751/312500000000 : ℝ)^777 := by
    have hnat : (531166047 : ℕ)^1033*312500000000^777 ≤ 134756994751^777*1000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531166047 1000000000 134756994751 312500000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33360831/156250000 : ℝ)^1033 ≤ (12837434370813/100000000000000 : ℝ)^777 := by
    have hnat : (33360831 : ℕ)^1033*100000000000000^777 ≤ 12837434370813^777*156250000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33360831 156250000 12837434370813 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396499813/10000000000 : ℝ)^1033 ≤ (2202016364211/5000000000000 : ℝ)^777 := by
    have hnat : (5396499813 : ℕ)^1033*5000000000000^777 ≤ 2202016364211^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396499813 10000000000 2202016364211 5000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531166047/1000000000 : ℝ), (-33360831/156250000 : ℝ), (5396499813/10000000000 : ℝ)] ![(134756994751/312500000000 : ℝ), (12837434370813/100000000000000 : ℝ), (2202016364211/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531166047/1000000000 : ℝ)|^1033 ≤ (134756994751/312500000000 : ℝ)^777
        have hw : |(531166047/1000000000 : ℝ)|=(531166047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33360831/156250000 : ℝ)|^1033 ≤ (12837434370813/100000000000000 : ℝ)^777
        have hw : |(-33360831/156250000 : ℝ)|=(33360831/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396499813/10000000000 : ℝ)|^1033 ≤ (2202016364211/5000000000000 : ℝ)^777
        have hw : |(5396499813/10000000000 : ℝ)|=(5396499813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s5_6 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2655830237/5000000000 : ℝ)*x 0 + (2698249903/5000000000 : ℝ)*x 1 + (-2135093189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655830237/5000000000 : ℝ)^1033 ≤ (43122238363493/100000000000000 : ℝ)^777 := by
    have hnat : (2655830237 : ℕ)^1033*100000000000000^777 ≤ 43122238363493^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655830237 5000000000 43122238363493 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698249903/5000000000 : ℝ)^1033 ≤ (2752520450517/6250000000000 : ℝ)^777 := by
    have hnat : (2698249903 : ℕ)^1033*6250000000000^777 ≤ 2752520450517^777*5000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698249903 5000000000 2752520450517 6250000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2135093189/10000000000 : ℝ)^1033 ≤ (12837434410781/100000000000000 : ℝ)^777 := by
    have hnat : (2135093189 : ℕ)^1033*100000000000000^777 ≤ 12837434410781^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135093189 10000000000 12837434410781 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655830237/5000000000 : ℝ), (2698249903/5000000000 : ℝ), (-2135093189/10000000000 : ℝ)] ![(43122238363493/100000000000000 : ℝ), (2752520450517/6250000000000 : ℝ), (12837434410781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655830237/5000000000 : ℝ)|^1033 ≤ (43122238363493/100000000000000 : ℝ)^777
        have hw : |(2655830237/5000000000 : ℝ)|=(2655830237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698249903/5000000000 : ℝ)|^1033 ≤ (2752520450517/6250000000000 : ℝ)^777
        have hw : |(2698249903/5000000000 : ℝ)|=(2698249903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2135093189/10000000000 : ℝ)|^1033 ≤ (12837434410781/100000000000000 : ℝ)^777
        have hw : |(-2135093189/10000000000 : ℝ)|=(2135093189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1071_s5_7 (p : ℝ) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2734159/6250000 : ℝ)*x 0 + (4508142739/10000000000 : ℝ)*x 1 + (4245186581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2734159/6250000 : ℝ)^1033 ≤ (33315370687803/100000000000000 : ℝ)^777 := by
    have hnat : (2734159 : ℕ)^1033*100000000000000^777 ≤ 33315370687803^777*6250000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734159 6250000 33315370687803 100000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508142739/10000000000 : ℝ)^1033 ≤ (270887828191/781250000000 : ℝ)^777 := by
    have hnat : (4508142739 : ℕ)^1033*781250000000^777 ≤ 270887828191^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508142739 10000000000 270887828191 781250000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245186581/10000000000 : ℝ)^1033 ≤ (6402197458177/20000000000000 : ℝ)^777 := by
    have hnat : (4245186581 : ℕ)^1033*20000000000000^777 ≤ 6402197458177^777*10000000000^1033 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245186581 10000000000 6402197458177 20000000000000 1033 777 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1033/256 : ℝ)) 1033 777 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2734159/6250000 : ℝ), (4508142739/10000000000 : ℝ), (4245186581/10000000000 : ℝ)] ![(33315370687803/100000000000000 : ℝ), (270887828191/781250000000 : ℝ), (6402197458177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2734159/6250000 : ℝ)|^1033 ≤ (33315370687803/100000000000000 : ℝ)^777
        have hw : |(2734159/6250000 : ℝ)|=(2734159/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508142739/10000000000 : ℝ)|^1033 ≤ (270887828191/781250000000 : ℝ)^777
        have hw : |(4508142739/10000000000 : ℝ)|=(4508142739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245186581/10000000000 : ℝ)|^1033 ≤ (6402197458177/20000000000000 : ℝ)^777
        have hw : |(4245186581/10000000000 : ℝ)|=(4245186581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1071_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5603/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (703/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11033/100000 : ℝ) ^ (8263/2048 : ℝ) ≤ (6863673390395219/50000000000000000000 : ℝ) := by
    have hpowers : (11033/100000 : ℝ)^8263 ≤ (6863673390395219/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11033 : ℕ)^8263*50000000000000000000^2048 ≤ 6863673390395219^2048*100000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11033 100000 6863673390395219 50000000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11033/100000 : ℝ)) (X := (6863673390395219/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7121/50000 : ℝ) ^ (8263/2048 : ℝ) ≤ (961346522462013/2500000000000000000 : ℝ) := by
    have hpowers : (7121/50000 : ℝ)^8263 ≤ (961346522462013/2500000000000000000 : ℝ)^2048 := by
      have hnat : (7121 : ℕ)^8263*2500000000000000000^2048 ≤ 961346522462013^2048*50000^8263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7121 50000 961346522462013 2500000000000000000 8263 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7121/50000 : ℝ)) (X := (961346522462013/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006863673390395219/25000000000000000000 : ℝ) ≤ (10000680399466129/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (25006863673390395219/25000000000000000000 : ℝ)^2048 ≤ (10000680399466129/10000000000000000 : ℝ)^8263 := by
      have hnat : (25006863673390395219 : ℕ)^2048*10000000000000000^8263 ≤ 10000680399466129^8263*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006863673390395219 25000000000000000000 10000680399466129 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000680399466129/10000000000000000 : ℝ)) (X := (25006863673390395219/25000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026090603839635479/50000000000000000000 : ℝ) ≤ (10001293067265099/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (50026090603839635479/50000000000000000000 : ℝ)^2048 ≤ (10001293067265099/10000000000000000 : ℝ)^8263 := by
      have hnat : (50026090603839635479 : ℕ)^2048*10000000000000000^8263 ≤ 10001293067265099^8263*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026090603839635479 50000000000000000000 10001293067265099 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001293067265099/10000000000000000 : ℝ)) (X := (50026090603839635479/50000000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250961346522462013/1250000000000000000 : ℝ) ≤ (10001905735064069/10000000000000000 : ℝ) ^ (8263/2048 : ℝ) := by
    have hpowers : (1250961346522462013/1250000000000000000 : ℝ)^2048 ≤ (10001905735064069/10000000000000000 : ℝ)^8263 := by
      have hnat : (1250961346522462013 : ℕ)^2048*10000000000000000^8263 ≤ 10001905735064069^8263*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250961346522462013 1250000000000000000 10001905735064069 10000000000000000 2048 8263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001905735064069/10000000000000000 : ℝ)) (X := (1250961346522462013/1250000000000000000 : ℝ)) (by norm_num) 8263 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6863673390395219/50000000000000000000 : ℝ) ≤ ((32078664274234735941/32090000000000000000 : ℝ)+2*(61266779897/32090000000000 : ℝ)*(11033/100000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (32078664274234735941/32090000000000000000 : ℝ)+2*(61266779897/32090000000000 : ℝ)*(11033/100000 : ℝ)=(10000680399466129/10000000000000000 : ℝ) by norm_num, show 1+2*(6863673390395219/50000000000000000000 : ℝ)=(25006863673390395219/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(961346522462013/2500000000000000000 : ℝ)+(6863673390395219/50000000000000000000 : ℝ) ≤ ((32078664274234735941/32090000000000000000 : ℝ)+(61266779897/32090000000000 : ℝ)*((7121/50000 : ℝ)+(11033/100000 : ℝ)))^(8263/2048 : ℝ) := by
    rw [show (32078664274234735941/32090000000000000000 : ℝ)+(61266779897/32090000000000 : ℝ)*((7121/50000 : ℝ)+(11033/100000 : ℝ))=(10001293067265099/10000000000000000 : ℝ) by norm_num, show 1+(961346522462013/2500000000000000000 : ℝ)+(6863673390395219/50000000000000000000 : ℝ)=(50026090603839635479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(961346522462013/2500000000000000000 : ℝ) ≤ ((32078664274234735941/32090000000000000000 : ℝ)+2*(61266779897/32090000000000 : ℝ)*(7121/50000 : ℝ))^(8263/2048 : ℝ) := by
    rw [show (32078664274234735941/32090000000000000000 : ℝ)+2*(61266779897/32090000000000 : ℝ)*(7121/50000 : ℝ)=(10001905735064069/10000000000000000 : ℝ) by norm_num, show 1+2*(961346522462013/2500000000000000000 : ℝ)=(1250961346522462013/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32078664274234735941/32090000000000000000 : ℝ)*(X 1 0+X 2 0)+(61266779897/32090000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (32078664274234735941/32090000000000000000 : ℝ)) (alpha := (61266779897/32090000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32078664274234735941/32090000000000000000 : ℝ)*(X 0 1+X 2 1)+(61266779897/32090000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (32078664274234735941/32090000000000000000 : ℝ)) (alpha := (61266779897/32090000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32078664274234735941/32090000000000000000 : ℝ)*(X 0 2+X 1 2)+(61266779897/32090000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8263/2048 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (32078664274234735941/32090000000000000000 : ℝ)) (alpha := (61266779897/32090000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1100540857/5000000000 : ℝ)*X 0 0+(5396851637/10000000000 : ℝ)*X 0 1+(5262111509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672805919/5000000000 : ℝ)*X 1 0+(-2269481479/10000000000 : ℝ)*X 1 1+(657763939/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334100739/625000000 : ℝ)*X 2 0+(526211151/1000000000 : ℝ)*X 2 1+(-2269481499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374643293/10000000000 : ℝ)*X 0 0+(2122248163/5000000000 : ℝ)*X 0 1+(4508830423/10000000000 : ℝ)*X 0 2+(4374643293/10000000000 : ℝ)*X 1 0+(2122248163/5000000000 : ℝ)*X 1 1+(4508830423/10000000000 : ℝ)*X 1 2+(4374643293/10000000000 : ℝ)*X 2 0+(2122248163/5000000000 : ℝ)*X 2 1+(4508830423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-110054369/500000000 : ℝ)*X 0 0+(5262462023/10000000000 : ℝ)*X 0 1+(2698249903/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531166047/1000000000 : ℝ)*X 1 0+(-33360831/156250000 : ℝ)*X 1 1+(5396499813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655830237/5000000000 : ℝ)*X 2 0+(2698249903/5000000000 : ℝ)*X 2 1+(-2135093189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2734159/6250000 : ℝ)*X 0 0+(4508142739/10000000000 : ℝ)*X 0 1+(4245186581/10000000000 : ℝ)*X 0 2+(2734159/6250000 : ℝ)*X 1 0+(4508142739/10000000000 : ℝ)*X 1 1+(4245186581/10000000000 : ℝ)*X 1 2+(2734159/6250000 : ℝ)*X 2 0+(4508142739/10000000000 : ℝ)*X 2 1+(4245186581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1071_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4344233894284797838529700843/401125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (431587593/20000000000000 : ℝ)*(base19) + (1986736143/100000000000000 : ℝ)*(base23) + (40563661/50000000000000 : ℝ)*(lower2) + (292451771/100000000000000 : ℝ)*(upper3) + (143958747/100000000000000 : ℝ)*(upper5) + (1400619769551259/25000000000000 : ℝ)*(major0) + (1400619769551259/25000000000000 : ℝ)*(major1) + (1400619769551259/25000000000000 : ℝ)*(major2) + (92771913656611/1250000000000 : ℝ)*(sp0) + (7421805417141211/100000000000000 : ℝ)*(sp1) + (927725698542879/12500000000000 : ℝ)*(sp2) + (945779710607023/25000000000000 : ℝ)*(sp3) + (10896510059/20000000000000 : ℝ)*(sp4) + (31377898629/100000000000000 : ℝ)*(sp7) + (1891575110163361/50000000000000 : ℝ)*(f.failure) + (296872303003167/4000000000000 : ℝ)*(f.sum) + (123119763579/80225000000000000000000000 : ℝ)*base65 + (3887096873974099719/802250000000000000000000000000000 : ℝ)*base67 + (9982556363378349719/802250000000000000000000000000000 : ℝ)*base69 + (3498370260789400281/802250000000000000000000000000000 : ℝ)*base72 + (7213742367999/1604500000000000000000000000 : ℝ)*base73 + (2106789218508849719/802250000000000000000000000000000 : ℝ)*base75 + (10309993201473099719/802250000000000000000000000000000 : ℝ)*base77 + (2846006849719650281/802250000000000000000000000000000 : ℝ)*base80 + (23096994126389/3209000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6389743/1000000000000000000000 : ℝ)*base89 + (6389743/1000000000000000000000 : ℝ)*base91 + (6389743/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6382548274243835955014081253/1604500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14786039/2000000000000 : ℝ)*(base19) + (401720497/50000000000000 : ℝ)*(base23) + (20110463/25000000000000 : ℝ)*(upper3) + (2758937/10000000000000 : ℝ)*(lower4) + (16917789/20000000000000 : ℝ)*(upper5) + (5631748815242411/100000000000000 : ℝ)*(major0) + (5631748815242411/100000000000000 : ℝ)*(major1) + (5631748815242411/100000000000000 : ℝ)*(major2) + (308246493/1562500000000 : ℝ)*(sp1) + (10378582421/50000000000000 : ℝ)*(sp2) + (7460582489406569/100000000000000 : ℝ)*(sp4) + (7460562022329067/100000000000000 : ℝ)*(sp5) + (7460560928800733/100000000000000 : ℝ)*(sp6) + (190145750424071/5000000000000 : ℝ)*(sp7) + (190145750424071/5000000000000 : ℝ)*(f.failure) + (7460582489406569/100000000000000 : ℝ)*(f.sum) + (2449710444157/1604500000000000000000000000 : ℝ)*base65 + (10197242452446806249/3209000000000000000000000000000000 : ℝ)*base68 + (3609846296349806249/3209000000000000000000000000000000 : ℝ)*base70 + (14930760049637806249/3209000000000000000000000000000000 : ℝ)*base72 + (4759917547631/1604500000000000000000000000 : ℝ)*base74 + (49153515323121193751/3209000000000000000000000000000000 : ℝ)*base75 + (24931779217093806249/3209000000000000000000000000000000 : ℝ)*base78 + (33658683987174193751/3209000000000000000000000000000000 : ℝ)*base79 + (18163054150591/3209000000000000000000000000 : ℝ)*base82 + (594473/100000000000000000000 : ℝ)*base89 + (594473/100000000000000000000 : ℝ)*base91 + (594473/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1071_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1071_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1071_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4181/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1071_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1071_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1071_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8263/2048 : ℝ) ≤ p) (hpb : p ≤ (1033/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29618063/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4181/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (273/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1071_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

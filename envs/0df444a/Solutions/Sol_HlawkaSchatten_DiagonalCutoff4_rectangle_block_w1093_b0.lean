-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1093_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:20.659883+00:00
-- url     : https://prove2.me/submissions/dc8d5568-c626-4a6a-89d9-15d2af6acfd3

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
theorem support_rectangle_w1093_s0_0 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-476854121/2500000000 : ℝ)*x 0 + (6065724883/10000000000 : ℝ)*x 1 + (4774243999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (476854121/2500000000 : ℝ)^4143 ≤ (11071548016359/100000000000000 : ℝ)^3119 := by
    have hnat : (476854121 : ℕ)^4143*100000000000000^3119 ≤ 11071548016359^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476854121 2500000000 11071548016359 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6065724883/10000000000 : ℝ)^4143 ≤ (12868883284221/25000000000000 : ℝ)^3119 := by
    have hnat : (6065724883 : ℕ)^4143*25000000000000^3119 ≤ 12868883284221^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6065724883 10000000000 12868883284221 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4774243999/10000000000 : ℝ)^4143 ≤ (18726459416991/50000000000000 : ℝ)^3119 := by
    have hnat : (4774243999 : ℕ)^4143*50000000000000^3119 ≤ 18726459416991^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774243999 10000000000 18726459416991 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-476854121/2500000000 : ℝ), (6065724883/10000000000 : ℝ), (4774243999/10000000000 : ℝ)] ![(11071548016359/100000000000000 : ℝ), (12868883284221/25000000000000 : ℝ), (18726459416991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-476854121/2500000000 : ℝ)|^4143 ≤ (11071548016359/100000000000000 : ℝ)^3119
        have hw : |(-476854121/2500000000 : ℝ)|=(476854121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6065724883/10000000000 : ℝ)|^4143 ≤ (12868883284221/25000000000000 : ℝ)^3119
        have hw : |(6065724883/10000000000 : ℝ)|=(6065724883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4774243999/10000000000 : ℝ)|^4143 ≤ (18726459416991/50000000000000 : ℝ)^3119
        have hw : |(4774243999/10000000000 : ℝ)|=(4774243999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s0_1 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5519553319/10000000000 : ℝ)*x 0 + (-662500873/2500000000 : ℝ)*x 1 + (4774243999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5519553319/10000000000 : ℝ)^4143 ≤ (22705879342773/50000000000000 : ℝ)^3119 := by
    have hnat : (5519553319 : ℕ)^4143*50000000000000^3119 ≤ 22705879342773^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519553319 10000000000 22705879342773 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (662500873/2500000000 : ℝ)^4143 ≤ (685412898617/4000000000000 : ℝ)^3119 := by
    have hnat : (662500873 : ℕ)^4143*4000000000000^3119 ≤ 685412898617^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662500873 2500000000 685412898617 4000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4774243999/10000000000 : ℝ)^4143 ≤ (18726459416991/50000000000000 : ℝ)^3119 := by
    have hnat : (4774243999 : ℕ)^4143*50000000000000^3119 ≤ 18726459416991^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774243999 10000000000 18726459416991 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5519553319/10000000000 : ℝ), (-662500873/2500000000 : ℝ), (4774243999/10000000000 : ℝ)] ![(22705879342773/50000000000000 : ℝ), (685412898617/4000000000000 : ℝ), (18726459416991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5519553319/10000000000 : ℝ)|^4143 ≤ (22705879342773/50000000000000 : ℝ)^3119
        have hw : |(5519553319/10000000000 : ℝ)|=(5519553319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-662500873/2500000000 : ℝ)|^4143 ≤ (685412898617/4000000000000 : ℝ)^3119
        have hw : |(-662500873/2500000000 : ℝ)|=(662500873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4774243999/10000000000 : ℝ)|^4143 ≤ (18726459416991/50000000000000 : ℝ)^3119
        have hw : |(4774243999/10000000000 : ℝ)|=(4774243999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s0_2 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5519553319/10000000000 : ℝ)*x 0 + (4774243999/10000000000 : ℝ)*x 1 + (-662500873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5519553319/10000000000 : ℝ)^4143 ≤ (22705879342773/50000000000000 : ℝ)^3119 := by
    have hnat : (5519553319 : ℕ)^4143*50000000000000^3119 ≤ 22705879342773^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519553319 10000000000 22705879342773 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4774243999/10000000000 : ℝ)^4143 ≤ (18726459416991/50000000000000 : ℝ)^3119 := by
    have hnat : (4774243999 : ℕ)^4143*50000000000000^3119 ≤ 18726459416991^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774243999 10000000000 18726459416991 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (662500873/2500000000 : ℝ)^4143 ≤ (685412898617/4000000000000 : ℝ)^3119 := by
    have hnat : (662500873 : ℕ)^4143*4000000000000^3119 ≤ 685412898617^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662500873 2500000000 685412898617 4000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5519553319/10000000000 : ℝ), (4774243999/10000000000 : ℝ), (-662500873/2500000000 : ℝ)] ![(22705879342773/50000000000000 : ℝ), (18726459416991/50000000000000 : ℝ), (685412898617/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5519553319/10000000000 : ℝ)|^4143 ≤ (22705879342773/50000000000000 : ℝ)^3119
        have hw : |(5519553319/10000000000 : ℝ)|=(5519553319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4774243999/10000000000 : ℝ)|^4143 ≤ (18726459416991/50000000000000 : ℝ)^3119
        have hw : |(4774243999/10000000000 : ℝ)|=(4774243999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-662500873/2500000000 : ℝ)|^4143 ≤ (685412898617/4000000000000 : ℝ)^3119
        have hw : |(-662500873/2500000000 : ℝ)|=(662500873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s0_3 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051245877/2500000000 : ℝ)*x 0 + (3123458803/10000000000 : ℝ)*x 1 + (708519449/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051245877/2500000000 : ℝ)^4143 ≤ (31640418504009/100000000000000 : ℝ)^3119 := by
    have hnat : (1051245877 : ℕ)^4143*100000000000000^3119 ≤ 31640418504009^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051245877 2500000000 31640418504009 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123458803/10000000000 : ℝ)^4143 ≤ (4263335118723/20000000000000 : ℝ)^3119 := by
    have hnat : (3123458803 : ℕ)^4143*20000000000000^3119 ≤ 4263335118723^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123458803 10000000000 4263335118723 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708519449/1250000000 : ℝ)^4143 ≤ (47042905891801/100000000000000 : ℝ)^3119 := by
    have hnat : (708519449 : ℕ)^4143*100000000000000^3119 ≤ 47042905891801^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708519449 1250000000 47042905891801 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051245877/2500000000 : ℝ), (3123458803/10000000000 : ℝ), (708519449/1250000000 : ℝ)] ![(31640418504009/100000000000000 : ℝ), (4263335118723/20000000000000 : ℝ), (47042905891801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051245877/2500000000 : ℝ)|^4143 ≤ (31640418504009/100000000000000 : ℝ)^3119
        have hw : |(1051245877/2500000000 : ℝ)|=(1051245877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3123458803/10000000000 : ℝ)|^4143 ≤ (4263335118723/20000000000000 : ℝ)^3119
        have hw : |(3123458803/10000000000 : ℝ)|=(3123458803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708519449/1250000000 : ℝ)|^4143 ≤ (47042905891801/100000000000000 : ℝ)^3119
        have hw : |(708519449/1250000000 : ℝ)|=(708519449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s0_4 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-478177157/2500000000 : ℝ)*x 0 + (2403790903/5000000000 : ℝ)*x 1 + (6031218289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (478177157/2500000000 : ℝ)^4143 ≤ (5556184885099/50000000000000 : ℝ)^3119 := by
    have hnat : (478177157 : ℕ)^4143*50000000000000^3119 ≤ 5556184885099^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478177157 2500000000 5556184885099 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2403790903/5000000000 : ℝ)^4143 ≤ (37800706682263/100000000000000 : ℝ)^3119 := by
    have hnat : (2403790903 : ℕ)^4143*100000000000000^3119 ≤ 37800706682263^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403790903 5000000000 37800706682263 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6031218289/10000000000 : ℝ)^4143 ≤ (25543461767699/50000000000000 : ℝ)^3119 := by
    have hnat : (6031218289 : ℕ)^4143*50000000000000^3119 ≤ 25543461767699^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6031218289 10000000000 25543461767699 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-478177157/2500000000 : ℝ), (2403790903/5000000000 : ℝ), (6031218289/10000000000 : ℝ)] ![(5556184885099/50000000000000 : ℝ), (37800706682263/100000000000000 : ℝ), (25543461767699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-478177157/2500000000 : ℝ)|^4143 ≤ (5556184885099/50000000000000 : ℝ)^3119
        have hw : |(-478177157/2500000000 : ℝ)|=(478177157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2403790903/5000000000 : ℝ)|^4143 ≤ (37800706682263/100000000000000 : ℝ)^3119
        have hw : |(2403790903/5000000000 : ℝ)|=(2403790903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6031218289/10000000000 : ℝ)|^4143 ≤ (25543461767699/50000000000000 : ℝ)^3119
        have hw : |(6031218289/10000000000 : ℝ)|=(6031218289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s0_5 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5168879507/10000000000 : ℝ)*x 0 + (-1393031297/10000000000 : ℝ)*x 1 + (3015608993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168879507/10000000000 : ℝ)^4143 ≤ (41619943007011/100000000000000 : ℝ)^3119 := by
    have hnat : (5168879507 : ℕ)^4143*100000000000000^3119 ≤ 41619943007011^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168879507 10000000000 41619943007011 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393031297/10000000000 : ℝ)^4143 ≤ (7293136862291/100000000000000 : ℝ)^3119 := by
    have hnat : (1393031297 : ℕ)^4143*100000000000000^3119 ≤ 7293136862291^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393031297 10000000000 7293136862291 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3015608993/5000000000 : ℝ)^4143 ≤ (25543460063121/50000000000000 : ℝ)^3119 := by
    have hnat : (3015608993 : ℕ)^4143*50000000000000^3119 ≤ 25543460063121^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015608993 5000000000 25543460063121 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168879507/10000000000 : ℝ), (-1393031297/10000000000 : ℝ), (3015608993/5000000000 : ℝ)] ![(41619943007011/100000000000000 : ℝ), (7293136862291/100000000000000 : ℝ), (25543460063121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168879507/10000000000 : ℝ)|^4143 ≤ (41619943007011/100000000000000 : ℝ)^3119
        have hw : |(5168879507/10000000000 : ℝ)|=(5168879507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1393031297/10000000000 : ℝ)|^4143 ≤ (7293136862291/100000000000000 : ℝ)^3119
        have hw : |(-1393031297/10000000000 : ℝ)|=(1393031297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3015608993/5000000000 : ℝ)|^4143 ≤ (25543460063121/50000000000000 : ℝ)^3119
        have hw : |(3015608993/5000000000 : ℝ)|=(3015608993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s0_6 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5168880227/10000000000 : ℝ)*x 0 + (1507804629/2500000000 : ℝ)*x 1 + (-1393029331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168880227/10000000000 : ℝ)^4143 ≤ (20809975353917/50000000000000 : ℝ)^3119 := by
    have hnat : (5168880227 : ℕ)^4143*50000000000000^3119 ≤ 20809975353917^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168880227 10000000000 20809975353917 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1507804629/2500000000 : ℝ)^4143 ≤ (12771731522363/25000000000000 : ℝ)^3119 := by
    have hnat : (1507804629 : ℕ)^4143*25000000000000^3119 ≤ 12771731522363^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507804629 2500000000 12771731522363 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1393029331/10000000000 : ℝ)^4143 ≤ (911640398769/12500000000000 : ℝ)^3119 := by
    have hnat : (1393029331 : ℕ)^4143*12500000000000^3119 ≤ 911640398769^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393029331 10000000000 911640398769 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168880227/10000000000 : ℝ), (1507804629/2500000000 : ℝ), (-1393029331/10000000000 : ℝ)] ![(20809975353917/50000000000000 : ℝ), (12771731522363/25000000000000 : ℝ), (911640398769/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168880227/10000000000 : ℝ)|^4143 ≤ (20809975353917/50000000000000 : ℝ)^3119
        have hw : |(5168880227/10000000000 : ℝ)|=(5168880227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1507804629/2500000000 : ℝ)|^4143 ≤ (12771731522363/25000000000000 : ℝ)^3119
        have hw : |(1507804629/2500000000 : ℝ)|=(1507804629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1393029331/10000000000 : ℝ)|^4143 ≤ (911640398769/12500000000000 : ℝ)^3119
        have hw : |(-1393029331/10000000000 : ℝ)|=(1393029331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s0_7 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4215408251/10000000000 : ℝ)*x 0 + (1400616851/2500000000 : ℝ)*x 1 + (638289917/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215408251/10000000000 : ℝ)^4143 ≤ (7936163728551/25000000000000 : ℝ)^3119 := by
    have hnat : (4215408251 : ℕ)^4143*25000000000000^3119 ≤ 7936163728551^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215408251 10000000000 7936163728551 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400616851/2500000000 : ℝ)^4143 ≤ (23160059660877/50000000000000 : ℝ)^3119 := by
    have hnat : (1400616851 : ℕ)^4143*50000000000000^3119 ≤ 23160059660877^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400616851 2500000000 23160059660877 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638289917/2000000000 : ℝ)^4143 ≤ (10967612871433/50000000000000 : ℝ)^3119 := by
    have hnat : (638289917 : ℕ)^4143*50000000000000^3119 ≤ 10967612871433^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638289917 2000000000 10967612871433 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215408251/10000000000 : ℝ), (1400616851/2500000000 : ℝ), (638289917/2000000000 : ℝ)] ![(7936163728551/25000000000000 : ℝ), (23160059660877/50000000000000 : ℝ), (10967612871433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215408251/10000000000 : ℝ)|^4143 ≤ (7936163728551/25000000000000 : ℝ)^3119
        have hw : |(4215408251/10000000000 : ℝ)|=(4215408251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1400616851/2500000000 : ℝ)|^4143 ≤ (23160059660877/50000000000000 : ℝ)^3119
        have hw : |(1400616851/2500000000 : ℝ)|=(1400616851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638289917/2000000000 : ℝ)|^4143 ≤ (10967612871433/50000000000000 : ℝ)^3119
        have hw : |(638289917/2000000000 : ℝ)|=(638289917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1093_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (21/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7001/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8285/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8285 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8285*1^2048 ≤ 0^2048*1^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8285/2048 : ℝ) ≤ (1227833424382178141/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8285 ≤ (1227833424382178141/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8285*50000000000000000000^2048 ≤ 1227833424382178141^2048*5^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1227833424382178141 50000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1227833424382178141/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8285 := by
      have hnat : (1 : ℕ)^2048*1^8285 ≤ 1^8285*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51227833424382178141/50000000000000000000 : ℝ) ≤ (5030074686875839/5000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (51227833424382178141/50000000000000000000 : ℝ)^2048 ≤ (5030074686875839/5000000000000000 : ℝ)^8285 := by
      have hnat : (51227833424382178141 : ℕ)^2048*5000000000000000^8285 ≤ 5030074686875839^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51227833424382178141 50000000000000000000 5030074686875839 5000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030074686875839/5000000000000000 : ℝ)) (X := (51227833424382178141/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26227833424382178141/25000000000000000000 : ℝ) ≤ (2530074686875839/2500000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (26227833424382178141/25000000000000000000 : ℝ)^2048 ≤ (2530074686875839/2500000000000000 : ℝ)^8285 := by
      have hnat : (26227833424382178141 : ℕ)^2048*2500000000000000^8285 ≤ 2530074686875839^8285*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26227833424382178141 25000000000000000000 2530074686875839 2500000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530074686875839/2500000000000000 : ℝ)) (X := (26227833424382178141/25000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30074686875839/2000000000000000 : ℝ)*(0 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30074686875839/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1227833424382178141/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30074686875839/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8285/2048 : ℝ) := by
    rw [show (1 : ℝ)+(30074686875839/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030074686875839/5000000000000000 : ℝ) by norm_num, show 1+(1227833424382178141/50000000000000000000 : ℝ)+(0 : ℝ)=(51227833424382178141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1227833424382178141/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30074686875839/2000000000000000 : ℝ)*(2/5 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30074686875839/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530074686875839/2500000000000000 : ℝ) by norm_num, show 1+2*(1227833424382178141/50000000000000000000 : ℝ)=(26227833424382178141/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30074686875839/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30074686875839/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30074686875839/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30074686875839/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30074686875839/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30074686875839/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-476854121/2500000000 : ℝ)*X 0 0+(6065724883/10000000000 : ℝ)*X 0 1+(4774243999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5519553319/10000000000 : ℝ)*X 1 0+(-662500873/2500000000 : ℝ)*X 1 1+(4774243999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5519553319/10000000000 : ℝ)*X 2 0+(4774243999/10000000000 : ℝ)*X 2 1+(-662500873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1051245877/2500000000 : ℝ)*X 0 0+(3123458803/10000000000 : ℝ)*X 0 1+(708519449/1250000000 : ℝ)*X 0 2+(1051245877/2500000000 : ℝ)*X 1 0+(3123458803/10000000000 : ℝ)*X 1 1+(708519449/1250000000 : ℝ)*X 1 2+(1051245877/2500000000 : ℝ)*X 2 0+(3123458803/10000000000 : ℝ)*X 2 1+(708519449/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-478177157/2500000000 : ℝ)*X 0 0+(2403790903/5000000000 : ℝ)*X 0 1+(6031218289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5168879507/10000000000 : ℝ)*X 1 0+(-1393031297/10000000000 : ℝ)*X 1 1+(3015608993/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168880227/10000000000 : ℝ)*X 2 0+(1507804629/2500000000 : ℝ)*X 2 1+(-1393029331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4215408251/10000000000 : ℝ)*X 0 0+(1400616851/2500000000 : ℝ)*X 0 1+(638289917/2000000000 : ℝ)*X 0 2+(4215408251/10000000000 : ℝ)*X 1 0+(1400616851/2500000000 : ℝ)*X 1 1+(638289917/2000000000 : ℝ)*X 1 2+(4215408251/10000000000 : ℝ)*X 2 0+(1400616851/2500000000 : ℝ)*X 2 1+(638289917/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (246918083439806396492313/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26373741/50000000000000 : ℝ)*(base1) + (1233731857/100000000000000 : ℝ)*(base19) + (57498169/5000000000000 : ℝ)*(base23) + (83768477/100000000000000 : ℝ)*(base24) + (279228257/100000000000000 : ℝ)*(upper3) + (583644721811663/100000000000000 : ℝ)*(major0) + (583644721811663/100000000000000 : ℝ)*(major1) + (583644721811663/100000000000000 : ℝ)*(major2) + (48394312287127/6250000000000 : ℝ)*(sp0) + (48394401091563/6250000000000 : ℝ)*(sp1) + (48394401091563/6250000000000 : ℝ)*(sp2) + (392975410289397/100000000000000 : ℝ)*(sp3) + (541470063/20000000000000 : ℝ)*(sp4) + (541194381/25000000000000 : ℝ)*(sp7) + (392977627814403/100000000000000 : ℝ)*(f.failure) + (154862330239373/20000000000000 : ℝ)*(f.sum) + (187567766089743/100000000000000000000000000000 : ℝ)*base66 + (69251703489743/200000000000000000000000000000 : ℝ)*base68 + (835452490289743/200000000000000000000000000000 : ℝ)*base70 + (997425727289743/200000000000000000000000000000 : ℝ)*base72 + (71753531989743/100000000000000000000000000000 : ℝ)*base74 + (28124888089743/200000000000000000000000000000 : ℝ)*base76 + (997425727289743/200000000000000000000000000000 : ℝ)*base78 + (113735672689743/200000000000000000000000000000 : ℝ)*base80 + (228948139689743/100000000000000000000000000000 : ℝ)*base82 + (18224243/5000000000000000000000 : ℝ)*base89 + (18224243/5000000000000000000000 : ℝ)*base91 + (18224243/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94423382755171248562983/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123397201/20000000000000 : ℝ)*(base19) + (579059053/50000000000000 : ℝ)*(base23) + (405922171/100000000000000 : ℝ)*(base39) + (41334887/25000000000000 : ℝ)*(base45) + (54766579/100000000000000 : ℝ)*(upper3) + (150229569/50000000000000 : ℝ)*(upper5) + (615997594842279/100000000000000 : ℝ)*(major0) + (615997594842279/100000000000000 : ℝ)*(major1) + (153999297230027/25000000000000 : ℝ)*(major2) + (97821211/20000000000000 : ℝ)*(sp2) + (51077079686407/6250000000000 : ℝ)*(sp4) + (204308164499127/25000000000000 : ℝ)*(sp5) + (817232033680523/100000000000000 : ℝ)*(sp6) + (414761351407563/100000000000000 : ℝ)*(sp7) + (414761351407563/100000000000000 : ℝ)*(f.failure) + (817233680904683/100000000000000 : ℝ)*(f.sum) + (89446608132307/200000000000000000000000000000 : ℝ)*base66 + (422014484582347/50000000000000000000000000000 : ℝ)*base68 + (151563796197081/200000000000000000000000000000 : ℝ)*base69 + (248355021832347/50000000000000000000000000000 : ℝ)*base72 + (886121967932307/200000000000000000000000000000 : ℝ)*base74 + (2497482387802919/200000000000000000000000000000 : ℝ)*base76 + (1346475055002919/200000000000000000000000000000 : ℝ)*base78 + (2348292392202919/200000000000000000000000000000 : ℝ)*base80 + (80773742597081/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16342203/5000000000000000000000 : ℝ)*base89 + (16342203/5000000000000000000000 : ℝ)*base91 + (16342203/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1093_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (21/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7001/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1093_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1093_s1_0 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-66112931/312500000 : ℝ)*x 0 + (285740517/500000000 : ℝ)*x 1 + (2495923037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66112931/312500000 : ℝ)^4143 ≤ (6352434195607/50000000000000 : ℝ)^3119 := by
    have hnat : (66112931 : ℕ)^4143*50000000000000^3119 ≤ 6352434195607^3119*312500000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66112931 312500000 6352434195607 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285740517/500000000 : ℝ)^4143 ≤ (4755793658981/10000000000000 : ℝ)^3119 := by
    have hnat : (285740517 : ℕ)^4143*10000000000000^3119 ≤ 4755793658981^3119*500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285740517 500000000 4755793658981 10000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2495923037/5000000000 : ℝ)^4143 ≤ (39737194998997/100000000000000 : ℝ)^3119 := by
    have hnat : (2495923037 : ℕ)^4143*100000000000000^3119 ≤ 39737194998997^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495923037 5000000000 39737194998997 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66112931/312500000 : ℝ), (285740517/500000000 : ℝ), (2495923037/5000000000 : ℝ)] ![(6352434195607/50000000000000 : ℝ), (4755793658981/10000000000000 : ℝ), (39737194998997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66112931/312500000 : ℝ)|^4143 ≤ (6352434195607/50000000000000 : ℝ)^3119
        have hw : |(-66112931/312500000 : ℝ)|=(66112931/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285740517/500000000 : ℝ)|^4143 ≤ (4755793658981/10000000000000 : ℝ)^3119
        have hw : |(285740517/500000000 : ℝ)|=(285740517/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2495923037/5000000000 : ℝ)|^4143 ≤ (39737194998997/100000000000000 : ℝ)^3119
        have hw : |(2495923037/5000000000 : ℝ)|=(2495923037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s1_1 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5421820459/10000000000 : ℝ)*x 0 + (-2506755357/10000000000 : ℝ)*x 1 + (2495923133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421820459/10000000000 : ℝ)^4143 ≤ (8869358743297/20000000000000 : ℝ)^3119 := by
    have hnat : (5421820459 : ℕ)^4143*20000000000000^3119 ≤ 8869358743297^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421820459 10000000000 8869358743297 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2506755357/10000000000 : ℝ)^4143 ≤ (7958004622393/50000000000000 : ℝ)^3119 := by
    have hnat : (2506755357 : ℕ)^4143*50000000000000^3119 ≤ 7958004622393^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506755357 10000000000 7958004622393 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2495923133/5000000000 : ℝ)^4143 ≤ (9934299257297/25000000000000 : ℝ)^3119 := by
    have hnat : (2495923133 : ℕ)^4143*25000000000000^3119 ≤ 9934299257297^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495923133 5000000000 9934299257297 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421820459/10000000000 : ℝ), (-2506755357/10000000000 : ℝ), (2495923133/5000000000 : ℝ)] ![(8869358743297/20000000000000 : ℝ), (7958004622393/50000000000000 : ℝ), (9934299257297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421820459/10000000000 : ℝ)|^4143 ≤ (8869358743297/20000000000000 : ℝ)^3119
        have hw : |(5421820459/10000000000 : ℝ)|=(5421820459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2506755357/10000000000 : ℝ)|^4143 ≤ (7958004622393/50000000000000 : ℝ)^3119
        have hw : |(-2506755357/10000000000 : ℝ)|=(2506755357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2495923133/5000000000 : ℝ)|^4143 ≤ (9934299257297/25000000000000 : ℝ)^3119
        have hw : |(2495923133/5000000000 : ℝ)|=(2495923133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s1_2 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5421821407/10000000000 : ℝ)*x 0 + (2495922653/5000000000 : ℝ)*x 1 + (-2506755339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421821407/10000000000 : ℝ)^4143 ≤ (8869360803239/20000000000000 : ℝ)^3119 := by
    have hnat : (5421821407 : ℕ)^4143*20000000000000^3119 ≤ 8869360803239^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421821407 10000000000 8869360803239 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495922653/5000000000 : ℝ)^4143 ≤ (7947437375647/20000000000000 : ℝ)^3119 := by
    have hnat : (2495922653 : ℕ)^4143*20000000000000^3119 ≤ 7947437375647^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495922653 5000000000 7947437375647 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2506755339/10000000000 : ℝ)^4143 ≤ (7958004546489/50000000000000 : ℝ)^3119 := by
    have hnat : (2506755339 : ℕ)^4143*50000000000000^3119 ≤ 7958004546489^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506755339 10000000000 7958004546489 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421821407/10000000000 : ℝ), (2495922653/5000000000 : ℝ), (-2506755339/10000000000 : ℝ)] ![(8869360803239/20000000000000 : ℝ), (7947437375647/20000000000000 : ℝ), (7958004546489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421821407/10000000000 : ℝ)|^4143 ≤ (8869360803239/20000000000000 : ℝ)^3119
        have hw : |(5421821407/10000000000 : ℝ)|=(5421821407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495922653/5000000000 : ℝ)|^4143 ≤ (7947437375647/20000000000000 : ℝ)^3119
        have hw : |(2495922653/5000000000 : ℝ)|=(2495922653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2506755339/10000000000 : ℝ)|^4143 ≤ (7958004546489/50000000000000 : ℝ)^3119
        have hw : |(-2506755339/10000000000 : ℝ)|=(2506755339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s1_3 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (432155871/1000000000 : ℝ)*x 0 + (36677443/100000000 : ℝ)*x 1 + (1018450161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432155871/1000000000 : ℝ)^4143 ≤ (32810843337589/100000000000000 : ℝ)^3119 := by
    have hnat : (432155871 : ℕ)^4143*100000000000000^3119 ≤ 32810843337589^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432155871 1000000000 32810843337589 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36677443/100000000 : ℝ)^4143 ≤ (1649175086831/6250000000000 : ℝ)^3119 := by
    have hnat : (36677443 : ℕ)^4143*6250000000000^3119 ≤ 1649175086831^3119*100000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36677443 100000000 1649175086831 6250000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018450161/2000000000 : ℝ)^4143 ≤ (1632094210443/4000000000000 : ℝ)^3119 := by
    have hnat : (1018450161 : ℕ)^4143*4000000000000^3119 ≤ 1632094210443^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018450161 2000000000 1632094210443 4000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432155871/1000000000 : ℝ), (36677443/100000000 : ℝ), (1018450161/2000000000 : ℝ)] ![(32810843337589/100000000000000 : ℝ), (1649175086831/6250000000000 : ℝ), (1632094210443/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432155871/1000000000 : ℝ)|^4143 ≤ (32810843337589/100000000000000 : ℝ)^3119
        have hw : |(432155871/1000000000 : ℝ)|=(432155871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36677443/100000000 : ℝ)|^4143 ≤ (1649175086831/6250000000000 : ℝ)^3119
        have hw : |(36677443/100000000 : ℝ)|=(36677443/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1018450161/2000000000 : ℝ)|^4143 ≤ (1632094210443/4000000000000 : ℝ)^3119
        have hw : |(1018450161/2000000000 : ℝ)|=(1018450161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s1_4 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116490903/10000000000 : ℝ)*x 0 + (625237967/1250000000 : ℝ)*x 1 + (570455033/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116490903/10000000000 : ℝ)^4143 ≤ (2542373096211/20000000000000 : ℝ)^3119 := by
    have hnat : (2116490903 : ℕ)^4143*20000000000000^3119 ≤ 2542373096211^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116490903 10000000000 2542373096211 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625237967/1250000000 : ℝ)^4143 ≤ (4980447370377/12500000000000 : ℝ)^3119 := by
    have hnat : (625237967 : ℕ)^4143*12500000000000^3119 ≤ 4980447370377^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625237967 1250000000 4980447370377 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570455033/1000000000 : ℝ)^4143 ≤ (23722277771641/50000000000000 : ℝ)^3119 := by
    have hnat : (570455033 : ℕ)^4143*50000000000000^3119 ≤ 23722277771641^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570455033 1000000000 23722277771641 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116490903/10000000000 : ℝ), (625237967/1250000000 : ℝ), (570455033/1000000000 : ℝ)] ![(2542373096211/20000000000000 : ℝ), (4980447370377/12500000000000 : ℝ), (23722277771641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116490903/10000000000 : ℝ)|^4143 ≤ (2542373096211/20000000000000 : ℝ)^3119
        have hw : |(-2116490903/10000000000 : ℝ)|=(2116490903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625237967/1250000000 : ℝ)|^4143 ≤ (4980447370377/12500000000000 : ℝ)^3119
        have hw : |(625237967/1250000000 : ℝ)|=(625237967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570455033/1000000000 : ℝ)|^4143 ≤ (23722277771641/50000000000000 : ℝ)^3119
        have hw : |(570455033/1000000000 : ℝ)|=(570455033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s1_5 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32730793/62500000 : ℝ)*x 0 + (-448512757/2500000000 : ℝ)*x 1 + (5704550169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32730793/62500000 : ℝ)^4143 ≤ (42349317849087/100000000000000 : ℝ)^3119 := by
    have hnat : (32730793 : ℕ)^4143*100000000000000^3119 ≤ 42349317849087^3119*62500000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32730793 62500000 42349317849087 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448512757/2500000000 : ℝ)^4143 ≤ (10206128366331/100000000000000 : ℝ)^3119 := by
    have hnat : (448512757 : ℕ)^4143*100000000000000^3119 ≤ 10206128366331^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448512757 2500000000 10206128366331 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5704550169/10000000000 : ℝ)^4143 ≤ (47444553764633/100000000000000 : ℝ)^3119 := by
    have hnat : (5704550169 : ℕ)^4143*100000000000000^3119 ≤ 47444553764633^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704550169 10000000000 47444553764633 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32730793/62500000 : ℝ), (-448512757/2500000000 : ℝ), (5704550169/10000000000 : ℝ)] ![(42349317849087/100000000000000 : ℝ), (10206128366331/100000000000000 : ℝ), (47444553764633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32730793/62500000 : ℝ)|^4143 ≤ (42349317849087/100000000000000 : ℝ)^3119
        have hw : |(32730793/62500000 : ℝ)|=(32730793/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448512757/2500000000 : ℝ)|^4143 ≤ (10206128366331/100000000000000 : ℝ)^3119
        have hw : |(-448512757/2500000000 : ℝ)|=(448512757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5704550169/10000000000 : ℝ)|^4143 ≤ (47444553764633/100000000000000 : ℝ)^3119
        have hw : |(5704550169/10000000000 : ℝ)|=(5704550169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s1_6 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52369269/100000000 : ℝ)*x 0 + (1426137573/2500000000 : ℝ)*x 1 + (-1794050819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52369269/100000000 : ℝ)^4143 ≤ (42349318063919/100000000000000 : ℝ)^3119 := by
    have hnat : (52369269 : ℕ)^4143*100000000000000^3119 ≤ 42349318063919^3119*100000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52369269 100000000 42349318063919 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426137573/2500000000 : ℝ)^4143 ≤ (47444555123477/100000000000000 : ℝ)^3119 := by
    have hnat : (1426137573 : ℕ)^4143*100000000000000^3119 ≤ 47444555123477^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426137573 2500000000 47444555123477 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1794050819/10000000000 : ℝ)^4143 ≤ (2551531696751/25000000000000 : ℝ)^3119 := by
    have hnat : (1794050819 : ℕ)^4143*25000000000000^3119 ≤ 2551531696751^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794050819 10000000000 2551531696751 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52369269/100000000 : ℝ), (1426137573/2500000000 : ℝ), (-1794050819/10000000000 : ℝ)] ![(42349318063919/100000000000000 : ℝ), (47444555123477/100000000000000 : ℝ), (2551531696751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52369269/100000000 : ℝ)|^4143 ≤ (42349318063919/100000000000000 : ℝ)^3119
        have hw : |(52369269/100000000 : ℝ)|=(52369269/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426137573/2500000000 : ℝ)|^4143 ≤ (47444555123477/100000000000000 : ℝ)^3119
        have hw : |(1426137573/2500000000 : ℝ)|=(1426137573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1794050819/10000000000 : ℝ)|^4143 ≤ (2551531696751/25000000000000 : ℝ)^3119
        have hw : |(-1794050819/10000000000 : ℝ)|=(1794050819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s1_7 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4323286041/10000000000 : ℝ)*x 0 + (2536217121/5000000000 : ℝ)*x 1 + (3687959591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323286041/10000000000 : ℝ)^4143 ≤ (32828264638951/100000000000000 : ℝ)^3119 := by
    have hnat : (4323286041 : ℕ)^4143*100000000000000^3119 ≤ 32828264638951^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323286041 10000000000 32828264638951 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536217121/5000000000 : ℝ)^4143 ≤ (8118315423541/20000000000000 : ℝ)^3119 := by
    have hnat : (2536217121 : ℕ)^4143*20000000000000^3119 ≤ 8118315423541^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536217121 5000000000 8118315423541 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3687959591/10000000000 : ℝ)^4143 ≤ (26580158223359/100000000000000 : ℝ)^3119 := by
    have hnat : (3687959591 : ℕ)^4143*100000000000000^3119 ≤ 26580158223359^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687959591 10000000000 26580158223359 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323286041/10000000000 : ℝ), (2536217121/5000000000 : ℝ), (3687959591/10000000000 : ℝ)] ![(32828264638951/100000000000000 : ℝ), (8118315423541/20000000000000 : ℝ), (26580158223359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323286041/10000000000 : ℝ)|^4143 ≤ (32828264638951/100000000000000 : ℝ)^3119
        have hw : |(4323286041/10000000000 : ℝ)|=(4323286041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2536217121/5000000000 : ℝ)|^4143 ≤ (8118315423541/20000000000000 : ℝ)^3119
        have hw : |(2536217121/5000000000 : ℝ)|=(2536217121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3687959591/10000000000 : ℝ)|^4143 ≤ (26580158223359/100000000000000 : ℝ)^3119
        have hw : |(3687959591/10000000000 : ℝ)|=(3687959591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1093_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20663/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7001/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (21/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7001/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (21/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7001/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (21/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7001/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (21/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7001/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (21/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7001/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (21/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (21/10000 : ℝ) ^ (8285/2048 : ℝ) ≤ (734934683/50000000000000000000 : ℝ) := by
    have hpowers : (21/10000 : ℝ)^8285 ≤ (734934683/50000000000000000000 : ℝ)^2048 := by
      have hnat : (21 : ℕ)^8285*50000000000000000000^2048 ≤ 734934683^2048*10000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21 10000 734934683 50000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21/10000 : ℝ)) (X := (734934683/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7001/25000 : ℝ) ^ (8285/2048 : ℝ) ≤ (580468227087131807/100000000000000000000 : ℝ) := by
    have hpowers : (7001/25000 : ℝ)^8285 ≤ (580468227087131807/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7001 : ℕ)^8285*100000000000000000000^2048 ≤ 580468227087131807^2048*25000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7001 25000 580468227087131807 100000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7001/25000 : ℝ)) (X := (580468227087131807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000734934683/25000000000000000000 : ℝ) ≤ (10000000000072669/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (25000000000734934683/25000000000000000000 : ℝ)^2048 ≤ (10000000000072669/10000000000000000 : ℝ)^8285 := by
      have hnat : (25000000000734934683 : ℕ)^2048*10000000000000000^8285 ≤ 10000000000072669^8285*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000734934683 25000000000000000000 10000000000072669 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000072669/10000000000000000 : ℝ)) (X := (25000000000734934683/25000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100580468228557001173/100000000000000000000 : ℝ) ≤ (5007158782731481/5000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (100580468228557001173/100000000000000000000 : ℝ)^2048 ≤ (5007158782731481/5000000000000000 : ℝ)^8285 := by
      have hnat : (100580468228557001173 : ℕ)^2048*5000000000000000^8285 ≤ 5007158782731481^8285*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100580468228557001173 100000000000000000000 5007158782731481 5000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007158782731481/5000000000000000 : ℝ)) (X := (100580468228557001173/100000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50580468227087131807/50000000000000000000 : ℝ) ≤ (2005727026170651/2000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50580468227087131807/50000000000000000000 : ℝ)^2048 ≤ (2005727026170651/2000000000000000 : ℝ)^8285 := by
      have hnat : (50580468227087131807 : ℕ)^2048*2000000000000000^8285 ≤ 2005727026170651^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50580468227087131807 50000000000000000000 2005727026170651 2000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005727026170651/2000000000000000 : ℝ)) (X := (50580468227087131807/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(734934683/50000000000000000000 : ℝ) ≤ ((138966993312277919563/138970000000000000000 : ℝ)+2*(14317565390293/2779400000000000 : ℝ)*(21/10000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (138966993312277919563/138970000000000000000 : ℝ)+2*(14317565390293/2779400000000000 : ℝ)*(21/10000 : ℝ)=(10000000000072669/10000000000000000 : ℝ) by norm_num, show 1+2*(734934683/50000000000000000000 : ℝ)=(25000000000734934683/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(580468227087131807/100000000000000000000 : ℝ)+(734934683/50000000000000000000 : ℝ) ≤ ((138966993312277919563/138970000000000000000 : ℝ)+(14317565390293/2779400000000000 : ℝ)*((7001/25000 : ℝ)+(21/10000 : ℝ)))^(8285/2048 : ℝ) := by
    rw [show (138966993312277919563/138970000000000000000 : ℝ)+(14317565390293/2779400000000000 : ℝ)*((7001/25000 : ℝ)+(21/10000 : ℝ))=(5007158782731481/5000000000000000 : ℝ) by norm_num, show 1+(580468227087131807/100000000000000000000 : ℝ)+(734934683/50000000000000000000 : ℝ)=(100580468228557001173/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(580468227087131807/100000000000000000000 : ℝ) ≤ ((138966993312277919563/138970000000000000000 : ℝ)+2*(14317565390293/2779400000000000 : ℝ)*(7001/25000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (138966993312277919563/138970000000000000000 : ℝ)+2*(14317565390293/2779400000000000 : ℝ)*(7001/25000 : ℝ)=(2005727026170651/2000000000000000 : ℝ) by norm_num, show 1+2*(580468227087131807/100000000000000000000 : ℝ)=(50580468227087131807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (138966993312277919563/138970000000000000000 : ℝ)*(X 1 0+X 2 0)+(14317565390293/2779400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (21/10000 : ℝ)) (hi := (7001/25000 : ℝ)) (c := (138966993312277919563/138970000000000000000 : ℝ)) (alpha := (14317565390293/2779400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (138966993312277919563/138970000000000000000 : ℝ)*(X 0 1+X 2 1)+(14317565390293/2779400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (21/10000 : ℝ)) (hi := (7001/25000 : ℝ)) (c := (138966993312277919563/138970000000000000000 : ℝ)) (alpha := (14317565390293/2779400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (138966993312277919563/138970000000000000000 : ℝ)*(X 0 2+X 1 2)+(14317565390293/2779400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (21/10000 : ℝ)) (hi := (7001/25000 : ℝ)) (c := (138966993312277919563/138970000000000000000 : ℝ)) (alpha := (14317565390293/2779400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66112931/312500000 : ℝ)*X 0 0+(285740517/500000000 : ℝ)*X 0 1+(2495923037/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421820459/10000000000 : ℝ)*X 1 0+(-2506755357/10000000000 : ℝ)*X 1 1+(2495923133/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5421821407/10000000000 : ℝ)*X 2 0+(2495922653/5000000000 : ℝ)*X 2 1+(-2506755339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((432155871/1000000000 : ℝ)*X 0 0+(36677443/100000000 : ℝ)*X 0 1+(1018450161/2000000000 : ℝ)*X 0 2+(432155871/1000000000 : ℝ)*X 1 0+(36677443/100000000 : ℝ)*X 1 1+(1018450161/2000000000 : ℝ)*X 1 2+(432155871/1000000000 : ℝ)*X 2 0+(36677443/100000000 : ℝ)*X 2 1+(1018450161/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2116490903/10000000000 : ℝ)*X 0 0+(625237967/1250000000 : ℝ)*X 0 1+(570455033/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((32730793/62500000 : ℝ)*X 1 0+(-448512757/2500000000 : ℝ)*X 1 1+(5704550169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((52369269/100000000 : ℝ)*X 2 0+(1426137573/2500000000 : ℝ)*X 2 1+(-1794050819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4323286041/10000000000 : ℝ)*X 0 0+(2536217121/5000000000 : ℝ)*X 0 1+(3687959591/10000000000 : ℝ)*X 0 2+(4323286041/10000000000 : ℝ)*X 1 0+(2536217121/5000000000 : ℝ)*X 1 1+(3687959591/10000000000 : ℝ)*X 1 2+(4323286041/10000000000 : ℝ)*X 2 0+(2536217121/5000000000 : ℝ)*X 2 1+(3687959591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11502525868717226812184036709/3474250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140200687/100000000000000 : ℝ)*(base1) + (37179767/6250000000000 : ℝ)*(base19) + (6536931/781250000000 : ℝ)*(base23) + (24932261/100000000000000 : ℝ)*(upper3) + (19279317/20000000000000 : ℝ)*(upper5) + (521299696458727/50000000000000 : ℝ)*(major0) + (521299696458727/50000000000000 : ℝ)*(major1) + (521299696458727/50000000000000 : ℝ)*(major2) + (691598104476831/50000000000000 : ℝ)*(sp0) + (691599347440331/50000000000000 : ℝ)*(sp1) + (691599226514883/50000000000000 : ℝ)*(sp2) + (350999194087281/50000000000000 : ℝ)*(sp3) + (3221003959/100000000000000 : ℝ)*(sp4) + (428671459/50000000000000 : ℝ)*(sp7) + (350999692859083/50000000000000 : ℝ)*(f.failure) + (691599644878467/50000000000000 : ℝ)*(f.sum) + (83251915746917/34742500000000000000000000000 : ℝ)*base66 + (3970145392161851823/534500000000000000000000000000000 : ℝ)*base68 + (5416276697398851823/534500000000000000000000000000000 : ℝ)*base70 + (3274951097193851823/534500000000000000000000000000000 : ℝ)*base72 + (406306089065659/69485000000000000000000000000 : ℝ)*base74 + (4012107052271851823/534500000000000000000000000000000 : ℝ)*base76 + (1945081372381851823/534500000000000000000000000000000 : ℝ)*base78 + (6382890414135851823/534500000000000000000000000000000 : ℝ)*base80 + (597872054681879/69485000000000000000000000000 : ℝ)*base82 + (12100677/2500000000000000000000 : ℝ)*base90 + (12100677/2500000000000000000000 : ℝ)*base92 + (12100677/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1342302026343175740170632377/267250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60816971/100000000000000 : ℝ)*(base1) + (1132111801/100000000000000 : ℝ)*(base19) + (1152264801/100000000000000 : ℝ)*(base23) + (112289793/100000000000000 : ℝ)*(upper3) + (56217383/50000000000000 : ℝ)*(upper5) + (536371610725691/50000000000000 : ℝ)*(major0) + (536371610725691/50000000000000 : ℝ)*(major1) + (536371610725691/50000000000000 : ℝ)*(major2) + (4439381271/100000000000000 : ℝ)*(sp1) + (1214055931/25000000000000 : ℝ)*(sp2) + (1423190613120269/100000000000000 : ℝ)*(sp4) + (711592490405113/50000000000000 : ℝ)*(sp5) + (1423184543814773/100000000000000 : ℝ)*(sp6) + (180573915590243/25000000000000 : ℝ)*(sp7) + (722295723177943/100000000000000 : ℝ)*(f.failure) + (711595276151649/50000000000000 : ℝ)*(f.sum) + (4916998033687/2672500000000000000000000000 : ℝ)*base66 + (1443934810364672541/534500000000000000000000000000000 : ℝ)*base67 + (3694023194381672541/534500000000000000000000000000000 : ℝ)*base69 + (549676382133827459/534500000000000000000000000000000 : ℝ)*base72 + (365445121377/2672500000000000000000000000 : ℝ)*base74 + (1222883503286672541/534500000000000000000000000000000 : ℝ)*base75 + (644846832549327459/534500000000000000000000000000000 : ℝ)*base78 + (2770628871842672541/534500000000000000000000000000000 : ℝ)*base79 + (9985685139073/2672500000000000000000000000 : ℝ)*base81 + (17761017/5000000000000000000000 : ℝ)*base90 + (17761017/5000000000000000000000 : ℝ)*base92 + (17761017/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1093_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20663/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1093_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1093_s2_0 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171522257/10000000000 : ℝ)*x 0 + (5520389951/10000000000 : ℝ)*x 1 + (160961469/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171522257/10000000000 : ℝ)^4143 ≤ (13152767142369/100000000000000 : ℝ)^3119 := by
    have hnat : (2171522257 : ℕ)^4143*100000000000000^3119 ≤ 13152767142369^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171522257 10000000000 13152767142369 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520389951/10000000000 : ℝ)^4143 ≤ (11355225529307/25000000000000 : ℝ)^3119 := by
    have hnat : (5520389951 : ℕ)^4143*25000000000000^3119 ≤ 11355225529307^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520389951 10000000000 11355225529307 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160961469/312500000 : ℝ)^4143 ≤ (20713165358613/50000000000000 : ℝ)^3119 := by
    have hnat : (160961469 : ℕ)^4143*50000000000000^3119 ≤ 20713165358613^3119*312500000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160961469 312500000 20713165358613 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171522257/10000000000 : ℝ), (5520389951/10000000000 : ℝ), (160961469/312500000 : ℝ)] ![(13152767142369/100000000000000 : ℝ), (11355225529307/25000000000000 : ℝ), (20713165358613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171522257/10000000000 : ℝ)|^4143 ≤ (13152767142369/100000000000000 : ℝ)^3119
        have hw : |(-2171522257/10000000000 : ℝ)|=(2171522257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520389951/10000000000 : ℝ)|^4143 ≤ (11355225529307/25000000000000 : ℝ)^3119
        have hw : |(5520389951/10000000000 : ℝ)|=(5520389951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160961469/312500000 : ℝ)|^4143 ≤ (20713165358613/50000000000000 : ℝ)^3119
        have hw : |(160961469/312500000 : ℝ)|=(160961469/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s2_1 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687999591/5000000000 : ℝ)*x 0 + (-94562709/400000000 : ℝ)*x 1 + (5150768043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687999591/5000000000 : ℝ)^4143 ≤ (21924826249689/50000000000000 : ℝ)^3119 := by
    have hnat : (2687999591 : ℕ)^4143*50000000000000^3119 ≤ 21924826249689^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687999591 5000000000 21924826249689 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94562709/400000000 : ℝ)^4143 ≤ (1840500714353/12500000000000 : ℝ)^3119 := by
    have hnat : (94562709 : ℕ)^4143*12500000000000^3119 ≤ 1840500714353^3119*400000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94562709 400000000 1840500714353 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150768043/10000000000 : ℝ)^4143 ≤ (5178292721801/12500000000000 : ℝ)^3119 := by
    have hnat : (5150768043 : ℕ)^4143*12500000000000^3119 ≤ 5178292721801^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150768043 10000000000 5178292721801 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687999591/5000000000 : ℝ), (-94562709/400000000 : ℝ), (5150768043/10000000000 : ℝ)] ![(21924826249689/50000000000000 : ℝ), (1840500714353/12500000000000 : ℝ), (5178292721801/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687999591/5000000000 : ℝ)|^4143 ≤ (21924826249689/50000000000000 : ℝ)^3119
        have hw : |(2687999591/5000000000 : ℝ)|=(2687999591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-94562709/400000000 : ℝ)|^4143 ≤ (1840500714353/12500000000000 : ℝ)^3119
        have hw : |(-94562709/400000000 : ℝ)|=(94562709/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150768043/10000000000 : ℝ)|^4143 ≤ (5178292721801/12500000000000 : ℝ)^3119
        have hw : |(5150768043/10000000000 : ℝ)|=(5150768043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s2_2 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375999131/10000000000 : ℝ)*x 0 + (515076809/1000000000 : ℝ)*x 1 + (-2364067731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375999131/10000000000 : ℝ)^4143 ≤ (21924825973411/50000000000000 : ℝ)^3119 := by
    have hnat : (5375999131 : ℕ)^4143*50000000000000^3119 ≤ 21924825973411^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375999131 10000000000 21924825973411 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515076809/1000000000 : ℝ)^4143 ≤ (20713171138261/50000000000000 : ℝ)^3119 := by
    have hnat : (515076809 : ℕ)^4143*50000000000000^3119 ≤ 20713171138261^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515076809 1000000000 20713171138261 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2364067731/10000000000 : ℝ)^4143 ≤ (7362002882231/50000000000000 : ℝ)^3119 := by
    have hnat : (2364067731 : ℕ)^4143*50000000000000^3119 ≤ 7362002882231^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364067731 10000000000 7362002882231 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375999131/10000000000 : ℝ), (515076809/1000000000 : ℝ), (-2364067731/10000000000 : ℝ)] ![(21924825973411/50000000000000 : ℝ), (20713171138261/50000000000000 : ℝ), (7362002882231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375999131/10000000000 : ℝ)|^4143 ≤ (21924825973411/50000000000000 : ℝ)^3119
        have hw : |(5375999131/10000000000 : ℝ)|=(5375999131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515076809/1000000000 : ℝ)|^4143 ≤ (20713171138261/50000000000000 : ℝ)^3119
        have hw : |(515076809/1000000000 : ℝ)|=(515076809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2364067731/10000000000 : ℝ)|^4143 ≤ (7362002882231/50000000000000 : ℝ)^3119
        have hw : |(-2364067731/10000000000 : ℝ)|=(2364067731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s2_3 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2179891503/5000000000 : ℝ)*x 0 + (100271957/250000000 : ℝ)*x 1 + (1184792759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179891503/5000000000 : ℝ)^4143 ≤ (1037402954303/3125000000000 : ℝ)^3119 := by
    have hnat : (2179891503 : ℕ)^4143*3125000000000^3119 ≤ 1037402954303^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179891503 5000000000 1037402954303 3125000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100271957/250000000 : ℝ)^4143 ≤ (29715216289477/100000000000000 : ℝ)^3119 := by
    have hnat : (100271957 : ℕ)^4143*100000000000000^3119 ≤ 29715216289477^3119*250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100271957 250000000 29715216289477 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184792759/2500000000 : ℝ)^4143 ≤ (7417577833131/20000000000000 : ℝ)^3119 := by
    have hnat : (1184792759 : ℕ)^4143*20000000000000^3119 ≤ 7417577833131^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184792759 2500000000 7417577833131 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179891503/5000000000 : ℝ), (100271957/250000000 : ℝ), (1184792759/2500000000 : ℝ)] ![(1037402954303/3125000000000 : ℝ), (29715216289477/100000000000000 : ℝ), (7417577833131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179891503/5000000000 : ℝ)|^4143 ≤ (1037402954303/3125000000000 : ℝ)^3119
        have hw : |(2179891503/5000000000 : ℝ)|=(2179891503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100271957/250000000 : ℝ)|^4143 ≤ (29715216289477/100000000000000 : ℝ)^3119
        have hw : |(100271957/250000000 : ℝ)|=(100271957/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1184792759/2500000000 : ℝ)|^4143 ≤ (7417577833131/20000000000000 : ℝ)^3119
        have hw : |(1184792759/2500000000 : ℝ)|=(1184792759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s2_4 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-542909781/2500000000 : ℝ)*x 0 + (1288351283/2500000000 : ℝ)*x 1 + (2758862357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542909781/2500000000 : ℝ)^4143 ≤ (52614829611/400000000000 : ℝ)^3119 := by
    have hnat : (542909781 : ℕ)^4143*400000000000^3119 ≤ 52614829611^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542909781 2500000000 52614829611 400000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288351283/2500000000 : ℝ)^4143 ≤ (8290903374429/20000000000000 : ℝ)^3119 := by
    have hnat : (1288351283 : ℕ)^4143*20000000000000^3119 ≤ 8290903374429^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288351283 2500000000 8290903374429 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2758862357/5000000000 : ℝ)^4143 ≤ (45391775706691/100000000000000 : ℝ)^3119 := by
    have hnat : (2758862357 : ℕ)^4143*100000000000000^3119 ≤ 45391775706691^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758862357 5000000000 45391775706691 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542909781/2500000000 : ℝ), (1288351283/2500000000 : ℝ), (2758862357/5000000000 : ℝ)] ![(52614829611/400000000000 : ℝ), (8290903374429/20000000000000 : ℝ), (45391775706691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542909781/2500000000 : ℝ)|^4143 ≤ (52614829611/400000000000 : ℝ)^3119
        have hw : |(-542909781/2500000000 : ℝ)|=(542909781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1288351283/2500000000 : ℝ)|^4143 ≤ (8290903374429/20000000000000 : ℝ)^3119
        have hw : |(1288351283/2500000000 : ℝ)|=(1288351283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2758862357/5000000000 : ℝ)|^4143 ≤ (45391775706691/100000000000000 : ℝ)^3119
        have hw : |(2758862357/5000000000 : ℝ)|=(2758862357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s2_5 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2641263629/5000000000 : ℝ)*x 0 + (-998555273/5000000000 : ℝ)*x 1 + (1379431201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641263629/5000000000 : ℝ)^4143 ≤ (42839838203213/100000000000000 : ℝ)^3119 := by
    have hnat : (2641263629 : ℕ)^4143*100000000000000^3119 ≤ 42839838203213^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641263629 5000000000 42839838203213 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998555273/5000000000 : ℝ)^4143 ≤ (11768385090927/100000000000000 : ℝ)^3119 := by
    have hnat : (998555273 : ℕ)^4143*100000000000000^3119 ≤ 11768385090927^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998555273 5000000000 11768385090927 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379431201/2500000000 : ℝ)^4143 ≤ (45391776690157/100000000000000 : ℝ)^3119 := by
    have hnat : (1379431201 : ℕ)^4143*100000000000000^3119 ≤ 45391776690157^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379431201 2500000000 45391776690157 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641263629/5000000000 : ℝ), (-998555273/5000000000 : ℝ), (1379431201/2500000000 : ℝ)] ![(42839838203213/100000000000000 : ℝ), (11768385090927/100000000000000 : ℝ), (45391776690157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641263629/5000000000 : ℝ)|^4143 ≤ (42839838203213/100000000000000 : ℝ)^3119
        have hw : |(2641263629/5000000000 : ℝ)|=(2641263629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-998555273/5000000000 : ℝ)|^4143 ≤ (11768385090927/100000000000000 : ℝ)^3119
        have hw : |(-998555273/5000000000 : ℝ)|=(998555273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379431201/2500000000 : ℝ)|^4143 ≤ (45391776690157/100000000000000 : ℝ)^3119
        have hw : |(1379431201/2500000000 : ℝ)|=(1379431201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s2_6 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5282527439/10000000000 : ℝ)*x 0 + (220708989/400000000 : ℝ)*x 1 + (-1997110407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282527439/10000000000 : ℝ)^4143 ≤ (42839840152987/100000000000000 : ℝ)^3119 := by
    have hnat : (5282527439 : ℕ)^4143*100000000000000^3119 ≤ 42839840152987^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282527439 10000000000 42839840152987 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220708989/400000000 : ℝ)^4143 ≤ (11347943956723/25000000000000 : ℝ)^3119 := by
    have hnat : (220708989 : ℕ)^4143*25000000000000^3119 ≤ 11347943956723^3119*400000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220708989 400000000 11347943956723 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997110407/10000000000 : ℝ)^4143 ≤ (5884192001463/50000000000000 : ℝ)^3119 := by
    have hnat : (1997110407 : ℕ)^4143*50000000000000^3119 ≤ 5884192001463^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997110407 10000000000 5884192001463 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282527439/10000000000 : ℝ), (220708989/400000000 : ℝ), (-1997110407/10000000000 : ℝ)] ![(42839840152987/100000000000000 : ℝ), (11347943956723/25000000000000 : ℝ), (5884192001463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282527439/10000000000 : ℝ)|^4143 ≤ (42839840152987/100000000000000 : ℝ)^3119
        have hw : |(5282527439/10000000000 : ℝ)|=(5282527439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220708989/400000000 : ℝ)|^4143 ≤ (11347943956723/25000000000000 : ℝ)^3119
        have hw : |(220708989/400000000 : ℝ)|=(220708989/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1997110407/10000000000 : ℝ)|^4143 ≤ (5884192001463/50000000000000 : ℝ)^3119
        have hw : |(-1997110407/10000000000 : ℝ)|=(1997110407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s2_7 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360014623/10000000000 : ℝ)*x 0 + (4733973537/10000000000 : ℝ)*x 1 + (401612827/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360014623/10000000000 : ℝ)^4143 ≤ (6639847436411/20000000000000 : ℝ)^3119 := by
    have hnat : (4360014623 : ℕ)^4143*20000000000000^3119 ≤ 6639847436411^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360014623 10000000000 6639847436411 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4733973537/10000000000 : ℝ)^4143 ≤ (18516935147883/50000000000000 : ℝ)^3119 := by
    have hnat : (4733973537 : ℕ)^4143*50000000000000^3119 ≤ 18516935147883^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4733973537 10000000000 18516935147883 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401612827/1000000000 : ℝ)^4143 ≤ (14883446254057/50000000000000 : ℝ)^3119 := by
    have hnat : (401612827 : ℕ)^4143*50000000000000^3119 ≤ 14883446254057^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401612827 1000000000 14883446254057 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360014623/10000000000 : ℝ), (4733973537/10000000000 : ℝ), (401612827/1000000000 : ℝ)] ![(6639847436411/20000000000000 : ℝ), (18516935147883/50000000000000 : ℝ), (14883446254057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360014623/10000000000 : ℝ)|^4143 ≤ (6639847436411/20000000000000 : ℝ)^3119
        have hw : |(4360014623/10000000000 : ℝ)|=(4360014623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4733973537/10000000000 : ℝ)|^4143 ≤ (18516935147883/50000000000000 : ℝ)^3119
        have hw : |(4733973537/10000000000 : ℝ)|=(4733973537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(401612827/1000000000 : ℝ)|^4143 ≤ (14883446254057/50000000000000 : ℝ)^3119
        have hw : |(401612827/1000000000 : ℝ)|=(401612827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1093_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8843/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16653/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (5371/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (364352891037259/50000000000000000000 : ℝ) := by
    have hpowers : (5371/100000 : ℝ)^8285 ≤ (364352891037259/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5371 : ℕ)^8285*50000000000000000000^2048 ≤ 364352891037259^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5371 100000 364352891037259 50000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5371/100000 : ℝ)) (X := (364352891037259/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20663/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (1357582759197187/800000000000000000 : ℝ) := by
    have hpowers : (20663/100000 : ℝ)^8285 ≤ (1357582759197187/800000000000000000 : ℝ)^2048 := by
      have hnat : (20663 : ℕ)^8285*800000000000000000^2048 ≤ 1357582759197187^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20663 100000 1357582759197187 800000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20663/100000 : ℝ)) (X := (1357582759197187/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000364352891037259/25000000000000000000 : ℝ) ≤ (10000036026101507/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (25000364352891037259/25000000000000000000 : ℝ)^2048 ≤ (10000036026101507/10000000000000000 : ℝ)^8285 := by
      have hnat : (25000364352891037259 : ℕ)^2048*10000000000000000^8285 ≤ 10000036026101507^8285*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000364352891037259 25000000000000000000 10000036026101507 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000036026101507/10000000000000000 : ℝ)) (X := (25000364352891037259/25000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100170426550681722893/100000000000000000000 : ℝ) ≤ (2000842027511473/2000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (100170426550681722893/100000000000000000000 : ℝ)^2048 ≤ (2000842027511473/2000000000000000 : ℝ)^8285 := by
      have hnat : (100170426550681722893 : ℕ)^2048*2000000000000000^8285 ≤ 2000842027511473^8285*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100170426550681722893 100000000000000000000 2000842027511473 2000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000842027511473/2000000000000000 : ℝ)) (X := (100170426550681722893/100000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (401357582759197187/400000000000000000 : ℝ) ≤ (10008384249013223/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (401357582759197187/400000000000000000 : ℝ)^2048 ≤ (10008384249013223/10000000000000000 : ℝ)^8285 := by
      have hnat : (401357582759197187 : ℕ)^2048*10000000000000000^8285 ≤ 10008384249013223^8285*400000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        401357582759197187 400000000000000000 10008384249013223 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008384249013223/10000000000000000 : ℝ)) (X := (401357582759197187/400000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(364352891037259/50000000000000000000 : ℝ) ≤ ((19109464075735677301/19115000000000000000 : ℝ)+2*(2087055727929/764600000000000 : ℝ)*(5371/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (19109464075735677301/19115000000000000000 : ℝ)+2*(2087055727929/764600000000000 : ℝ)*(5371/100000 : ℝ)=(10000036026101507/10000000000000000 : ℝ) by norm_num, show 1+2*(364352891037259/50000000000000000000 : ℝ)=(25000364352891037259/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1357582759197187/800000000000000000 : ℝ)+(364352891037259/50000000000000000000 : ℝ) ≤ ((19109464075735677301/19115000000000000000 : ℝ)+(2087055727929/764600000000000 : ℝ)*((20663/100000 : ℝ)+(5371/100000 : ℝ)))^(8285/2048 : ℝ) := by
    rw [show (19109464075735677301/19115000000000000000 : ℝ)+(2087055727929/764600000000000 : ℝ)*((20663/100000 : ℝ)+(5371/100000 : ℝ))=(2000842027511473/2000000000000000 : ℝ) by norm_num, show 1+(1357582759197187/800000000000000000 : ℝ)+(364352891037259/50000000000000000000 : ℝ)=(100170426550681722893/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1357582759197187/800000000000000000 : ℝ) ≤ ((19109464075735677301/19115000000000000000 : ℝ)+2*(2087055727929/764600000000000 : ℝ)*(20663/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (19109464075735677301/19115000000000000000 : ℝ)+2*(2087055727929/764600000000000 : ℝ)*(20663/100000 : ℝ)=(10008384249013223/10000000000000000 : ℝ) by norm_num, show 1+2*(1357582759197187/800000000000000000 : ℝ)=(401357582759197187/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19109464075735677301/19115000000000000000 : ℝ)*(X 1 0+X 2 0)+(2087055727929/764600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (5371/100000 : ℝ)) (hi := (20663/100000 : ℝ)) (c := (19109464075735677301/19115000000000000000 : ℝ)) (alpha := (2087055727929/764600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19109464075735677301/19115000000000000000 : ℝ)*(X 0 1+X 2 1)+(2087055727929/764600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (5371/100000 : ℝ)) (hi := (20663/100000 : ℝ)) (c := (19109464075735677301/19115000000000000000 : ℝ)) (alpha := (2087055727929/764600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19109464075735677301/19115000000000000000 : ℝ)*(X 0 2+X 1 2)+(2087055727929/764600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (5371/100000 : ℝ)) (hi := (20663/100000 : ℝ)) (c := (19109464075735677301/19115000000000000000 : ℝ)) (alpha := (2087055727929/764600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2171522257/10000000000 : ℝ)*X 0 0+(5520389951/10000000000 : ℝ)*X 0 1+(160961469/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687999591/5000000000 : ℝ)*X 1 0+(-94562709/400000000 : ℝ)*X 1 1+(5150768043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375999131/10000000000 : ℝ)*X 2 0+(515076809/1000000000 : ℝ)*X 2 1+(-2364067731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179891503/5000000000 : ℝ)*X 0 0+(100271957/250000000 : ℝ)*X 0 1+(1184792759/2500000000 : ℝ)*X 0 2+(2179891503/5000000000 : ℝ)*X 1 0+(100271957/250000000 : ℝ)*X 1 1+(1184792759/2500000000 : ℝ)*X 1 2+(2179891503/5000000000 : ℝ)*X 2 0+(100271957/250000000 : ℝ)*X 2 1+(1184792759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-542909781/2500000000 : ℝ)*X 0 0+(1288351283/2500000000 : ℝ)*X 0 1+(2758862357/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2641263629/5000000000 : ℝ)*X 1 0+(-998555273/5000000000 : ℝ)*X 1 1+(1379431201/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5282527439/10000000000 : ℝ)*X 2 0+(220708989/400000000 : ℝ)*X 2 1+(-1997110407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360014623/10000000000 : ℝ)*X 0 0+(4733973537/10000000000 : ℝ)*X 0 1+(401612827/1000000000 : ℝ)*X 0 2+(4360014623/10000000000 : ℝ)*X 1 0+(4733973537/10000000000 : ℝ)*X 1 1+(401612827/1000000000 : ℝ)*X 1 2+(4360014623/10000000000 : ℝ)*X 2 0+(4733973537/10000000000 : ℝ)*X 2 1+(401612827/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12525092789742014210988081/3733398437500000000000000000000 : ℝ) := by norm_num
    linear_combination (23905113/100000000000000 : ℝ)*(base29) + (90080039/100000000000000 : ℝ)*(upper2) + (19777157/100000000000000 : ℝ)*(upper3) + (76282127/100000000000000 : ℝ)*(upper4) + (30164967/100000000000000 : ℝ)*(upper5) + (20392756437301/1000000000000 : ℝ)*(major0) + (509818916908803/25000000000000 : ℝ)*(major1) + (509818916908803/25000000000000 : ℝ)*(major2) + (1352733243843379/50000000000000 : ℝ)*(sp0) + (1352736610912481/50000000000000 : ℝ)*(sp1) + (1352736610912481/50000000000000 : ℝ)*(sp2) + (42908630090369/3125000000000 : ℝ)*(sp3) + (1689510829/25000000000000 : ℝ)*(sp4) + (1814819297/100000000000000 : ℝ)*(sp7) + (2681792925217/195312500000 : ℝ)*(f.failure) + (108218929829203/4000000000000 : ℝ)*(f.sum) + (184883539365261/19115000000000000000000000000 : ℝ)*base66 + (4466918082455769297/477875000000000000000000000000000 : ℝ)*base68 + (1598688757448394297/477875000000000000000000000000000 : ℝ)*base70 + (285125680498353399/19115000000000000000000000000000 : ℝ)*base72 + (198590053313373/19115000000000000000000000000 : ℝ)*base74 + (723134937970805703/477875000000000000000000000000000 : ℝ)*base75 + (11531288918223399/19115000000000000000000000000000 : ℝ)*base78 + (4388573352441069297/477875000000000000000000000000000 : ℝ)*base80 + (19174021598841/2389375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (322217/39062500000000000000 : ℝ)*base90 + (8551/4882812500000000000 : ℝ)*base91 + (8551/4882812500000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18808831184590405943900643/5973437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (617276013/100000000000000 : ℝ)*(base19) + (391546567/50000000000000 : ℝ)*(base23) + (26373263/25000000000000 : ℝ)*(upper3) + (16863599/100000000000000 : ℝ)*(lower4) + (52223603/100000000000000 : ℝ)*(upper5) + (51723759654463/2500000000000 : ℝ)*(major0) + (51723759654463/2500000000000 : ℝ)*(major1) + (51723759654463/2500000000000 : ℝ)*(major2) + (333640509/6250000000000 : ℝ)*(sp1) + (7590078671/100000000000000 : ℝ)*(sp2) + (1372421105865097/50000000000000 : ℝ)*(sp4) + (686209064051509/25000000000000 : ℝ)*(sp5) + (2744833838558389/100000000000000 : ℝ)*(sp6) + (21766538369823/1562500000000 : ℝ)*(sp7) + (21766538369823/1562500000000 : ℝ)*(f.failure) + (1372421105865097/50000000000000 : ℝ)*(f.sum) + (523285736323/955750000000000000000000000 : ℝ)*base66 + (230704110104919363/47787500000000000000000000000000 : ℝ)*base67 + (44125791886730637/47787500000000000000000000000000 : ℝ)*base70 + (251976731021919363/47787500000000000000000000000000 : ℝ)*base71 + (2313911461881/955750000000000000000000000 : ℝ)*base73 + (560043703835019363/47787500000000000000000000000000 : ℝ)*base75 + (93196875998819363/47787500000000000000000000000000 : ℝ)*base77 + (318684682040406863/47787500000000000000000000000000 : ℝ)*base79 + (261506620873/191150000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (672737/78125000000000000000 : ℝ)*base90 + (672737/78125000000000000000 : ℝ)*base92 + (672737/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1093_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16653/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1093_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1093_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16653/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1093_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1093_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1093_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16653/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1093_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

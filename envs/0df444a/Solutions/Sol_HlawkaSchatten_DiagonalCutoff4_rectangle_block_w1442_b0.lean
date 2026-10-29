-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1442_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:57:21.804246+00:00
-- url     : https://prove2.me/submissions/46e07885-a290-4ddd-a14d-a6749599eb70

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
theorem support_rectangle_w1442_s0_0 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-175147647/1000000000 : ℝ)*x 0 + (5954834787/10000000000 : ℝ)*x 1 + (4834202123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175147647/1000000000 : ℝ)^2201 ≤ (161388083691/1562500000000 : ℝ)^1689 := by
    have hnat : (175147647 : ℕ)^2201*1562500000000^1689 ≤ 161388083691^1689*1000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175147647 1000000000 161388083691 1562500000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5954834787/10000000000 : ℝ)^2201 ≤ (10177806259477/20000000000000 : ℝ)^1689 := by
    have hnat : (5954834787 : ℕ)^2201*20000000000000^1689 ≤ 10177806259477^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5954834787 10000000000 10177806259477 20000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4834202123/10000000000 : ℝ)^2201 ≤ (19391065666867/50000000000000 : ℝ)^1689 := by
    have hnat : (4834202123 : ℕ)^2201*50000000000000^1689 ≤ 19391065666867^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4834202123 10000000000 19391065666867 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-175147647/1000000000 : ℝ), (5954834787/10000000000 : ℝ), (4834202123/10000000000 : ℝ)] ![(161388083691/1562500000000 : ℝ), (10177806259477/20000000000000 : ℝ), (19391065666867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-175147647/1000000000 : ℝ)|^2201 ≤ (161388083691/1562500000000 : ℝ)^1689
        have hw : |(-175147647/1000000000 : ℝ)|=(175147647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5954834787/10000000000 : ℝ)|^2201 ≤ (10177806259477/20000000000000 : ℝ)^1689
        have hw : |(5954834787/10000000000 : ℝ)|=(5954834787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4834202123/10000000000 : ℝ)|^2201 ≤ (19391065666867/50000000000000 : ℝ)^1689
        have hw : |(4834202123/10000000000 : ℝ)|=(4834202123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s0_1 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (686331857/1250000000 : ℝ)*x 0 + (-1191975187/5000000000 : ℝ)*x 1 + (604275247/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (686331857/1250000000 : ℝ)^2201 ≤ (2289097787757/5000000000000 : ℝ)^1689 := by
    have hnat : (686331857 : ℕ)^2201*5000000000000^1689 ≤ 2289097787757^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686331857 1250000000 2289097787757 5000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1191975187/5000000000 : ℝ)^2201 ≤ (7717957219751/50000000000000 : ℝ)^1689 := by
    have hnat : (1191975187 : ℕ)^2201*50000000000000^1689 ≤ 7717957219751^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191975187 5000000000 7717957219751 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604275247/1250000000 : ℝ)^2201 ≤ (38782129796943/100000000000000 : ℝ)^1689 := by
    have hnat : (604275247 : ℕ)^2201*100000000000000^1689 ≤ 38782129796943^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604275247 1250000000 38782129796943 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(686331857/1250000000 : ℝ), (-1191975187/5000000000 : ℝ), (604275247/1250000000 : ℝ)] ![(2289097787757/5000000000000 : ℝ), (7717957219751/50000000000000 : ℝ), (38782129796943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(686331857/1250000000 : ℝ)|^2201 ≤ (2289097787757/5000000000000 : ℝ)^1689
        have hw : |(686331857/1250000000 : ℝ)|=(686331857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1191975187/5000000000 : ℝ)|^2201 ≤ (7717957219751/50000000000000 : ℝ)^1689
        have hw : |(-1191975187/5000000000 : ℝ)|=(1191975187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(604275247/1250000000 : ℝ)|^2201 ≤ (38782129796943/100000000000000 : ℝ)^1689
        have hw : |(604275247/1250000000 : ℝ)|=(604275247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s0_2 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5490654759/10000000000 : ℝ)*x 0 + (2417100971/5000000000 : ℝ)*x 1 + (-119197527/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5490654759/10000000000 : ℝ)^2201 ≤ (1144548867529/2500000000000 : ℝ)^1689 := by
    have hnat : (5490654759 : ℕ)^2201*2500000000000^1689 ≤ 1144548867529^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490654759 10000000000 1144548867529 2500000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2417100971/5000000000 : ℝ)^2201 ≤ (7756425888299/20000000000000 : ℝ)^1689 := by
    have hnat : (2417100971 : ℕ)^2201*20000000000000^1689 ≤ 7756425888299^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417100971 5000000000 7756425888299 20000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119197527/500000000 : ℝ)^2201 ≤ (3087183168033/20000000000000 : ℝ)^1689 := by
    have hnat : (119197527 : ℕ)^2201*20000000000000^1689 ≤ 3087183168033^1689*500000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119197527 500000000 3087183168033 20000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5490654759/10000000000 : ℝ), (2417100971/5000000000 : ℝ), (-119197527/500000000 : ℝ)] ![(1144548867529/2500000000000 : ℝ), (7756425888299/20000000000000 : ℝ), (3087183168033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5490654759/10000000000 : ℝ)|^2201 ≤ (1144548867529/2500000000000 : ℝ)^1689
        have hw : |(5490654759/10000000000 : ℝ)|=(5490654759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2417100971/5000000000 : ℝ)|^2201 ≤ (7756425888299/20000000000000 : ℝ)^1689
        have hw : |(2417100971/5000000000 : ℝ)|=(2417100971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-119197527/500000000 : ℝ)|^2201 ≤ (3087183168033/20000000000000 : ℝ)^1689
        have hw : |(-119197527/500000000 : ℝ)|=(119197527/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s0_3 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (416414251/1000000000 : ℝ)*x 0 + (3103058657/10000000000 : ℝ)*x 1 + (173091069/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416414251/1000000000 : ℝ)^2201 ≤ (15964648219047/50000000000000 : ℝ)^1689 := by
    have hnat : (416414251 : ℕ)^2201*50000000000000^1689 ≤ 15964648219047^1689*1000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416414251 1000000000 15964648219047 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103058657/10000000000 : ℝ)^2201 ≤ (10881837760399/50000000000000 : ℝ)^1689 := by
    have hnat : (3103058657 : ℕ)^2201*50000000000000^1689 ≤ 10881837760399^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103058657 10000000000 10881837760399 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173091069/312500000 : ℝ)^2201 ≤ (11576757005421/25000000000000 : ℝ)^1689 := by
    have hnat : (173091069 : ℕ)^2201*25000000000000^1689 ≤ 11576757005421^1689*312500000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173091069 312500000 11576757005421 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416414251/1000000000 : ℝ), (3103058657/10000000000 : ℝ), (173091069/312500000 : ℝ)] ![(15964648219047/50000000000000 : ℝ), (10881837760399/50000000000000 : ℝ), (11576757005421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416414251/1000000000 : ℝ)|^2201 ≤ (15964648219047/50000000000000 : ℝ)^1689
        have hw : |(416414251/1000000000 : ℝ)|=(416414251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103058657/10000000000 : ℝ)|^2201 ≤ (10881837760399/50000000000000 : ℝ)^1689
        have hw : |(3103058657/10000000000 : ℝ)|=(3103058657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(173091069/312500000 : ℝ)|^2201 ≤ (11576757005421/25000000000000 : ℝ)^1689
        have hw : |(173091069/312500000 : ℝ)|=(173091069/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s0_4 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-109714513/625000000 : ℝ)*x 0 + (4862845273/10000000000 : ℝ)*x 1 + (592516867/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109714513/625000000 : ℝ)^2201 ≤ (32372647373/312500000000 : ℝ)^1689 := by
    have hnat : (109714513 : ℕ)^2201*312500000000^1689 ≤ 32372647373^1689*625000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109714513 625000000 32372647373 312500000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4862845273/10000000000 : ℝ)^2201 ≤ (19540922777911/50000000000000 : ℝ)^1689 := by
    have hnat : (4862845273 : ℕ)^2201*50000000000000^1689 ≤ 19540922777911^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862845273 10000000000 19540922777911 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (592516867/1000000000 : ℝ)^2201 ≤ (12639726818869/25000000000000 : ℝ)^1689 := by
    have hnat : (592516867 : ℕ)^2201*25000000000000^1689 ≤ 12639726818869^1689*1000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592516867 1000000000 12639726818869 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109714513/625000000 : ℝ), (4862845273/10000000000 : ℝ), (592516867/1000000000 : ℝ)] ![(32372647373/312500000000 : ℝ), (19540922777911/50000000000000 : ℝ), (12639726818869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109714513/625000000 : ℝ)|^2201 ≤ (32372647373/312500000000 : ℝ)^1689
        have hw : |(-109714513/625000000 : ℝ)|=(109714513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4862845273/10000000000 : ℝ)|^2201 ≤ (19540922777911/50000000000000 : ℝ)^1689
        have hw : |(4862845273/10000000000 : ℝ)|=(4862845273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(592516867/1000000000 : ℝ)|^2201 ≤ (12639726818869/25000000000000 : ℝ)^1689
        have hw : |(592516867/1000000000 : ℝ)|=(592516867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s0_5 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1036946451/2000000000 : ℝ)*x 0 + (-1292983821/10000000000 : ℝ)*x 1 + (2962584369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036946451/2000000000 : ℝ)^2201 ≤ (42486314454637/100000000000000 : ℝ)^1689 := by
    have hnat : (1036946451 : ℕ)^2201*100000000000000^1689 ≤ 42486314454637^1689*2000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036946451 2000000000 42486314454637 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292983821/10000000000 : ℝ)^2201 ≤ (6954777494097/100000000000000 : ℝ)^1689 := by
    have hnat : (1292983821 : ℕ)^2201*100000000000000^1689 ≤ 6954777494097^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292983821 10000000000 6954777494097 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2962584369/5000000000 : ℝ)^2201 ≤ (25279454015803/50000000000000 : ℝ)^1689 := by
    have hnat : (2962584369 : ℕ)^2201*50000000000000^1689 ≤ 25279454015803^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2962584369 5000000000 25279454015803 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036946451/2000000000 : ℝ), (-1292983821/10000000000 : ℝ), (2962584369/5000000000 : ℝ)] ![(42486314454637/100000000000000 : ℝ), (6954777494097/100000000000000 : ℝ), (25279454015803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036946451/2000000000 : ℝ)|^2201 ≤ (42486314454637/100000000000000 : ℝ)^1689
        have hw : |(1036946451/2000000000 : ℝ)|=(1036946451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1292983821/10000000000 : ℝ)|^2201 ≤ (6954777494097/100000000000000 : ℝ)^1689
        have hw : |(-1292983821/10000000000 : ℝ)|=(1292983821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2962584369/5000000000 : ℝ)|^2201 ≤ (25279454015803/50000000000000 : ℝ)^1689
        have hw : |(2962584369/5000000000 : ℝ)|=(2962584369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s0_6 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2592366141/5000000000 : ℝ)*x 0 + (740646073/1250000000 : ℝ)*x 1 + (-161623003/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592366141/5000000000 : ℝ)^2201 ≤ (21243157371479/50000000000000 : ℝ)^1689 := by
    have hnat : (2592366141 : ℕ)^2201*50000000000000^1689 ≤ 21243157371479^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592366141 5000000000 21243157371479 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (740646073/1250000000 : ℝ)^2201 ≤ (25279453159597/50000000000000 : ℝ)^1689 := by
    have hnat : (740646073 : ℕ)^2201*50000000000000^1689 ≤ 25279453159597^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740646073 1250000000 25279453159597 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161623003/1250000000 : ℝ)^2201 ≤ (1738694729251/25000000000000 : ℝ)^1689 := by
    have hnat : (161623003 : ℕ)^2201*25000000000000^1689 ≤ 1738694729251^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161623003 1250000000 1738694729251 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592366141/5000000000 : ℝ), (740646073/1250000000 : ℝ), (-161623003/1250000000 : ℝ)] ![(21243157371479/50000000000000 : ℝ), (25279453159597/50000000000000 : ℝ), (1738694729251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592366141/5000000000 : ℝ)|^2201 ≤ (21243157371479/50000000000000 : ℝ)^1689
        have hw : |(2592366141/5000000000 : ℝ)|=(2592366141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(740646073/1250000000 : ℝ)|^2201 ≤ (25279453159597/50000000000000 : ℝ)^1689
        have hw : |(740646073/1250000000 : ℝ)|=(740646073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-161623003/1250000000 : ℝ)|^2201 ≤ (1738694729251/25000000000000 : ℝ)^1689
        have hw : |(-161623003/1250000000 : ℝ)|=(161623003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s0_7 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4172740099/10000000000 : ℝ)*x 0 + (1095330767/2000000000 : ℝ)*x 1 + (3167542459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4172740099/10000000000 : ℝ)^2201 ≤ (32015230761117/100000000000000 : ℝ)^1689 := by
    have hnat : (4172740099 : ℕ)^2201*100000000000000^1689 ≤ 32015230761117^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172740099 10000000000 32015230761117 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095330767/2000000000 : ℝ)^2201 ≤ (4562988268593/10000000000000 : ℝ)^1689 := by
    have hnat : (1095330767 : ℕ)^2201*10000000000000^1689 ≤ 4562988268593^1689*2000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095330767 2000000000 4562988268593 10000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167542459/10000000000 : ℝ)^2201 ≤ (1397180408257/6250000000000 : ℝ)^1689 := by
    have hnat : (3167542459 : ℕ)^2201*6250000000000^1689 ≤ 1397180408257^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167542459 10000000000 1397180408257 6250000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4172740099/10000000000 : ℝ), (1095330767/2000000000 : ℝ), (3167542459/10000000000 : ℝ)] ![(32015230761117/100000000000000 : ℝ), (4562988268593/10000000000000 : ℝ), (1397180408257/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4172740099/10000000000 : ℝ)|^2201 ≤ (32015230761117/100000000000000 : ℝ)^1689
        have hw : |(4172740099/10000000000 : ℝ)|=(4172740099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095330767/2000000000 : ℝ)|^2201 ≤ (4562988268593/10000000000000 : ℝ)^1689
        have hw : |(1095330767/2000000000 : ℝ)|=(1095330767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167542459/10000000000 : ℝ)|^2201 ≤ (1397180408257/6250000000000 : ℝ)^1689
        have hw : |(3167542459/10000000000 : ℝ)|=(3167542459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1442_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2139/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26169/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4401/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4401 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4401*1^1024 ≤ 0^1024*1^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4401/1024 : ℝ) ≤ (974278045653101927/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4401 ≤ (974278045653101927/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4401*50000000000000000000^1024 ≤ 974278045653101927^1024*5^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 974278045653101927 50000000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (974278045653101927/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4401 := by
      have hnat : (1 : ℕ)^1024*1^4401 ≤ 1^4401*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50974278045653101927/50000000000000000000 : ℝ) ≤ (10045002808465971/10000000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (50974278045653101927/50000000000000000000 : ℝ)^1024 ≤ (10045002808465971/10000000000000000 : ℝ)^4401 := by
      have hnat : (50974278045653101927 : ℕ)^1024*10000000000000000^4401 ≤ 10045002808465971^4401*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50974278045653101927 50000000000000000000 10045002808465971 10000000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045002808465971/10000000000000000 : ℝ)) (X := (50974278045653101927/50000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25974278045653101927/25000000000000000000 : ℝ) ≤ (5045002808465971/5000000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (25974278045653101927/25000000000000000000 : ℝ)^1024 ≤ (5045002808465971/5000000000000000 : ℝ)^4401 := by
      have hnat : (25974278045653101927 : ℕ)^1024*5000000000000000^4401 ≤ 5045002808465971^4401*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25974278045653101927 25000000000000000000 5045002808465971 5000000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045002808465971/5000000000000000 : ℝ)) (X := (25974278045653101927/25000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(45002808465971/4000000000000000 : ℝ)*(0 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45002808465971/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(974278045653101927/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(45002808465971/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4401/1024 : ℝ) := by
    rw [show (1 : ℝ)+(45002808465971/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10045002808465971/10000000000000000 : ℝ) by norm_num, show 1+(974278045653101927/50000000000000000000 : ℝ)+(0 : ℝ)=(50974278045653101927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(974278045653101927/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(45002808465971/4000000000000000 : ℝ)*(2/5 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45002808465971/4000000000000000 : ℝ)*(2/5 : ℝ)=(5045002808465971/5000000000000000 : ℝ) by norm_num, show 1+2*(974278045653101927/50000000000000000000 : ℝ)=(25974278045653101927/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(45002808465971/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45002808465971/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(45002808465971/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45002808465971/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(45002808465971/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45002808465971/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-175147647/1000000000 : ℝ)*X 0 0+(5954834787/10000000000 : ℝ)*X 0 1+(4834202123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((686331857/1250000000 : ℝ)*X 1 0+(-1191975187/5000000000 : ℝ)*X 1 1+(604275247/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5490654759/10000000000 : ℝ)*X 2 0+(2417100971/5000000000 : ℝ)*X 2 1+(-119197527/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((416414251/1000000000 : ℝ)*X 0 0+(3103058657/10000000000 : ℝ)*X 0 1+(173091069/312500000 : ℝ)*X 0 2+(416414251/1000000000 : ℝ)*X 1 0+(3103058657/10000000000 : ℝ)*X 1 1+(173091069/312500000 : ℝ)*X 1 2+(416414251/1000000000 : ℝ)*X 2 0+(3103058657/10000000000 : ℝ)*X 2 1+(173091069/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109714513/625000000 : ℝ)*X 0 0+(4862845273/10000000000 : ℝ)*X 0 1+(592516867/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1036946451/2000000000 : ℝ)*X 1 0+(-1292983821/10000000000 : ℝ)*X 1 1+(2962584369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2592366141/5000000000 : ℝ)*X 2 0+(740646073/1250000000 : ℝ)*X 2 1+(-161623003/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4172740099/10000000000 : ℝ)*X 0 0+(1095330767/2000000000 : ℝ)*X 0 1+(3167542459/10000000000 : ℝ)*X 0 2+(4172740099/10000000000 : ℝ)*X 1 0+(1095330767/2000000000 : ℝ)*X 1 1+(3167542459/10000000000 : ℝ)*X 1 2+(4172740099/10000000000 : ℝ)*X 2 0+(1095330767/2000000000 : ℝ)*X 2 1+(3167542459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132608725083052084216557/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14314927/10000000000000 : ℝ)*(base1) + (599339631/50000000000000 : ℝ)*(base19) + (1182914509/100000000000000 : ℝ)*(base23) + (96153/62500000000 : ℝ)*(upper3) + (2085257/2000000000000 : ℝ)*(upper5) + (325724266472189/50000000000000 : ℝ)*(major0) + (325724266472189/50000000000000 : ℝ)*(major1) + (325724266472189/50000000000000 : ℝ)*(major2) + (892356742842721/100000000000000 : ℝ)*(sp0) + (446179456059331/50000000000000 : ℝ)*(sp1) + (446179463941707/50000000000000 : ℝ)*(sp2) + (410534896092383/100000000000000 : ℝ)*(sp3) + (438888059/12500000000000 : ℝ)*(sp4) + (869518771/50000000000000 : ℝ)*(sp7) + (82107355655839/20000000000000 : ℝ)*(f.failure) + (892360110797923/100000000000000 : ℝ)*(f.sum) + (64740130180519/100000000000000000000000000000 : ℝ)*base65 + (1398536872419481/200000000000000000000000000000 : ℝ)*base68 + (671693448619481/200000000000000000000000000000 : ℝ)*base70 + (952085107619481/200000000000000000000000000000 : ℝ)*base72 + (252511336919481/100000000000000000000000000000 : ℝ)*base74 + (1608150886419481/200000000000000000000000000000 : ℝ)*base76 + (175634018419481/200000000000000000000000000000 : ℝ)*base78 + (389235613419481/200000000000000000000000000000 : ℝ)*base80 + (188613963819481/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9047943/2000000000000000000000 : ℝ)*base89 + (9047943/2000000000000000000000 : ℝ)*base91 + (9047943/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (855333907978378180807137/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (977052153/50000000000000 : ℝ)*(base19) + (1970635503/100000000000000 : ℝ)*(base23) + (35064623/20000000000000 : ℝ)*(base32) + (146669613/50000000000000 : ℝ)*(upper3) + (180446463/100000000000000 : ℝ)*(upper5) + (343599799416151/50000000000000 : ℝ)*(major0) + (343599799416151/50000000000000 : ℝ)*(major1) + (343599799416151/50000000000000 : ℝ)*(major2) + (4668578201/100000000000000 : ℝ)*(sp1) + (973133791/20000000000000 : ℝ)*(sp2) + (470666073306043/50000000000000 : ℝ)*(sp4) + (941325523929579/100000000000000 : ℝ)*(sp5) + (941325310307629/100000000000000 : ℝ)*(sp6) + (27066661913631/6250000000000 : ℝ)*(sp7) + (433066765941211/100000000000000 : ℝ)*(f.failure) + (470666073306043/50000000000000 : ℝ)*(f.sum) + (155090810302379/100000000000000000000000000000 : ℝ)*base66 + (727972223697621/200000000000000000000000000000 : ℝ)*base67 + (251170985502379/200000000000000000000000000000 : ℝ)*base70 + (682413489702379/200000000000000000000000000000 : ℝ)*base72 + (281059788597621/100000000000000000000000000000 : ℝ)*base73 + (113132842897621/200000000000000000000000000000 : ℝ)*base75 + (1160457794102379/200000000000000000000000000000 : ℝ)*base78 + (578638530097621/200000000000000000000000000000 : ℝ)*base79 + (39892424497621/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (22152093/10000000000000000000000 : ℝ)*base90 + (22152093/10000000000000000000000 : ℝ)*base92 + (22152093/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1442_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2139/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26169/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1442_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1442_s1_0 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-240248851/1250000000 : ℝ)*x 0 + (2800034157/5000000000 : ℝ)*x 1 + (1269908303/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240248851/1250000000 : ℝ)^2201 ≤ (2331627346141/20000000000000 : ℝ)^1689 := by
    have hnat : (240248851 : ℕ)^2201*20000000000000^1689 ≤ 2331627346141^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240248851 1250000000 2331627346141 20000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2800034157/5000000000 : ℝ)^2201 ≤ (46974391741637/100000000000000 : ℝ)^1689 := by
    have hnat : (2800034157 : ℕ)^2201*100000000000000^1689 ≤ 46974391741637^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800034157 5000000000 46974391741637 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269908303/2500000000 : ℝ)^2201 ≤ (10341867877993/25000000000000 : ℝ)^1689 := by
    have hnat : (1269908303 : ℕ)^2201*25000000000000^1689 ≤ 10341867877993^1689*2500000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269908303 2500000000 10341867877993 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-240248851/1250000000 : ℝ), (2800034157/5000000000 : ℝ), (1269908303/2500000000 : ℝ)] ![(2331627346141/20000000000000 : ℝ), (46974391741637/100000000000000 : ℝ), (10341867877993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-240248851/1250000000 : ℝ)|^2201 ≤ (2331627346141/20000000000000 : ℝ)^1689
        have hw : |(-240248851/1250000000 : ℝ)|=(240248851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2800034157/5000000000 : ℝ)|^2201 ≤ (46974391741637/100000000000000 : ℝ)^1689
        have hw : |(2800034157/5000000000 : ℝ)|=(2800034157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269908303/2500000000 : ℝ)|^2201 ≤ (10341867877993/25000000000000 : ℝ)^1689
        have hw : |(1269908303/2500000000 : ℝ)|=(1269908303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s1_1 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5395511841/10000000000 : ℝ)*x 0 + (-2197492187/10000000000 : ℝ)*x 1 + (2539817377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395511841/10000000000 : ℝ)^2201 ≤ (44750879644871/100000000000000 : ℝ)^1689 := by
    have hnat : (5395511841 : ℕ)^2201*100000000000000^1689 ≤ 44750879644871^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395511841 10000000000 44750879644871 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197492187/10000000000 : ℝ)^2201 ≤ (6940816229341/50000000000000 : ℝ)^1689 := by
    have hnat : (2197492187 : ℕ)^2201*50000000000000^1689 ≤ 6940816229341^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197492187 10000000000 6940816229341 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539817377/5000000000 : ℝ)^2201 ≤ (20683743938211/50000000000000 : ℝ)^1689 := by
    have hnat : (2539817377 : ℕ)^2201*50000000000000^1689 ≤ 20683743938211^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539817377 5000000000 20683743938211 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395511841/10000000000 : ℝ), (-2197492187/10000000000 : ℝ), (2539817377/5000000000 : ℝ)] ![(44750879644871/100000000000000 : ℝ), (6940816229341/50000000000000 : ℝ), (20683743938211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395511841/10000000000 : ℝ)|^2201 ≤ (44750879644871/100000000000000 : ℝ)^1689
        have hw : |(5395511841/10000000000 : ℝ)|=(5395511841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197492187/10000000000 : ℝ)|^2201 ≤ (6940816229341/50000000000000 : ℝ)^1689
        have hw : |(-2197492187/10000000000 : ℝ)|=(2197492187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539817377/5000000000 : ℝ)|^2201 ≤ (20683743938211/50000000000000 : ℝ)^1689
        have hw : |(2539817377/5000000000 : ℝ)|=(2539817377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s1_2 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5395513091/10000000000 : ℝ)*x 0 + (1269908337/2500000000 : ℝ)*x 1 + (-1098746179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395513091/10000000000 : ℝ)^2201 ≤ (22375446577653/50000000000000 : ℝ)^1689 := by
    have hnat : (5395513091 : ℕ)^2201*50000000000000^1689 ≤ 22375446577653^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395513091 10000000000 22375446577653 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269908337/2500000000 : ℝ)^2201 ≤ (41367472955269/100000000000000 : ℝ)^1689 := by
    have hnat : (1269908337 : ℕ)^2201*100000000000000^1689 ≤ 41367472955269^1689*2500000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269908337 2500000000 41367472955269 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098746179/5000000000 : ℝ)^2201 ≤ (3470408466587/25000000000000 : ℝ)^1689 := by
    have hnat : (1098746179 : ℕ)^2201*25000000000000^1689 ≤ 3470408466587^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098746179 5000000000 3470408466587 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395513091/10000000000 : ℝ), (1269908337/2500000000 : ℝ), (-1098746179/5000000000 : ℝ)] ![(22375446577653/50000000000000 : ℝ), (41367472955269/100000000000000 : ℝ), (3470408466587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395513091/10000000000 : ℝ)|^2201 ≤ (22375446577653/50000000000000 : ℝ)^1689
        have hw : |(5395513091/10000000000 : ℝ)|=(5395513091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269908337/2500000000 : ℝ)|^2201 ≤ (41367472955269/100000000000000 : ℝ)^1689
        have hw : |(1269908337/2500000000 : ℝ)|=(1269908337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1098746179/5000000000 : ℝ)|^2201 ≤ (3470408466587/25000000000000 : ℝ)^1689
        have hw : |(-1098746179/5000000000 : ℝ)|=(1098746179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s1_3 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267141967/625000000 : ℝ)*x 0 + (1870939403/5000000000 : ℝ)*x 1 + (1218278829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267141967/625000000 : ℝ)^2201 ≤ (33034093667749/100000000000000 : ℝ)^1689 := by
    have hnat : (267141967 : ℕ)^2201*100000000000000^1689 ≤ 33034093667749^1689*625000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267141967 625000000 33034093667749 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870939403/5000000000 : ℝ)^2201 ≤ (6944116804241/25000000000000 : ℝ)^1689 := by
    have hnat : (1870939403 : ℕ)^2201*25000000000000^1689 ≤ 6944116804241^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870939403 5000000000 6944116804241 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1218278829/2500000000 : ℝ)^2201 ≤ (9797359773981/25000000000000 : ℝ)^1689 := by
    have hnat : (1218278829 : ℕ)^2201*25000000000000^1689 ≤ 9797359773981^1689*2500000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218278829 2500000000 9797359773981 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267141967/625000000 : ℝ), (1870939403/5000000000 : ℝ), (1218278829/2500000000 : ℝ)] ![(33034093667749/100000000000000 : ℝ), (6944116804241/25000000000000 : ℝ), (9797359773981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267141967/625000000 : ℝ)|^2201 ≤ (33034093667749/100000000000000 : ℝ)^1689
        have hw : |(267141967/625000000 : ℝ)|=(267141967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1870939403/5000000000 : ℝ)|^2201 ≤ (6944116804241/25000000000000 : ℝ)^1689
        have hw : |(1870939403/5000000000 : ℝ)|=(1870939403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1218278829/2500000000 : ℝ)|^2201 ≤ (9797359773981/25000000000000 : ℝ)^1689
        have hw : |(1218278829/2500000000 : ℝ)|=(1218278829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s1_4 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1922371553/10000000000 : ℝ)*x 0 + (203426969/400000000 : ℝ)*x 1 + (699240737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922371553/10000000000 : ℝ)^2201 ≤ (5830573188571/50000000000000 : ℝ)^1689 := by
    have hnat : (1922371553 : ℕ)^2201*50000000000000^1689 ≤ 5830573188571^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922371553 10000000000 5830573188571 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203426969/400000000 : ℝ)^2201 ≤ (41431593213891/100000000000000 : ℝ)^1689 := by
    have hnat : (203426969 : ℕ)^2201*100000000000000^1689 ≤ 41431593213891^1689*400000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203426969 400000000 41431593213891 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (699240737/1250000000 : ℝ)^2201 ≤ (2345363019621/5000000000000 : ℝ)^1689 := by
    have hnat : (699240737 : ℕ)^2201*5000000000000^1689 ≤ 2345363019621^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699240737 1250000000 2345363019621 5000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1922371553/10000000000 : ℝ), (203426969/400000000 : ℝ), (699240737/1250000000 : ℝ)] ![(5830573188571/50000000000000 : ℝ), (41431593213891/100000000000000 : ℝ), (2345363019621/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1922371553/10000000000 : ℝ)|^2201 ≤ (5830573188571/50000000000000 : ℝ)^1689
        have hw : |(-1922371553/10000000000 : ℝ)|=(1922371553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203426969/400000000 : ℝ)|^2201 ≤ (41431593213891/100000000000000 : ℝ)^1689
        have hw : |(203426969/400000000 : ℝ)|=(203426969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(699240737/1250000000 : ℝ)|^2201 ≤ (2345363019621/5000000000000 : ℝ)^1689
        have hw : |(699240737/1250000000 : ℝ)|=(699240737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s1_5 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5259406749/10000000000 : ℝ)*x 0 + (-1683200523/10000000000 : ℝ)*x 1 + (34962037/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259406749/10000000000 : ℝ)^2201 ≤ (8657093256823/20000000000000 : ℝ)^1689 := by
    have hnat : (5259406749 : ℕ)^2201*20000000000000^1689 ≤ 8657093256823^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259406749 10000000000 8657093256823 20000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1683200523/10000000000 : ℝ)^2201 ≤ (4903636520697/50000000000000 : ℝ)^1689 := by
    have hnat : (1683200523 : ℕ)^2201*50000000000000^1689 ≤ 4903636520697^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683200523 10000000000 4903636520697 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34962037/62500000 : ℝ)^2201 ≤ (11726815163669/25000000000000 : ℝ)^1689 := by
    have hnat : (34962037 : ℕ)^2201*25000000000000^1689 ≤ 11726815163669^1689*62500000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34962037 62500000 11726815163669 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259406749/10000000000 : ℝ), (-1683200523/10000000000 : ℝ), (34962037/62500000 : ℝ)] ![(8657093256823/20000000000000 : ℝ), (4903636520697/50000000000000 : ℝ), (11726815163669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259406749/10000000000 : ℝ)|^2201 ≤ (8657093256823/20000000000000 : ℝ)^1689
        have hw : |(5259406749/10000000000 : ℝ)|=(5259406749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1683200523/10000000000 : ℝ)|^2201 ≤ (4903636520697/50000000000000 : ℝ)^1689
        have hw : |(-1683200523/10000000000 : ℝ)|=(1683200523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34962037/62500000 : ℝ)|^2201 ≤ (11726815163669/25000000000000 : ℝ)^1689
        have hw : |(34962037/62500000 : ℝ)|=(34962037/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s1_6 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5259406671/10000000000 : ℝ)*x 0 + (139848147/250000000 : ℝ)*x 1 + (-1683200691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259406671/10000000000 : ℝ)^2201 ≤ (2705341590473/6250000000000 : ℝ)^1689 := by
    have hnat : (5259406671 : ℕ)^2201*6250000000000^1689 ≤ 2705341590473^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259406671 10000000000 2705341590473 6250000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139848147/250000000 : ℝ)^2201 ≤ (46907260217583/100000000000000 : ℝ)^1689 := by
    have hnat : (139848147 : ℕ)^2201*100000000000000^1689 ≤ 46907260217583^1689*250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139848147 250000000 46907260217583 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1683200691/10000000000 : ℝ)^2201 ≤ (9807274316987/100000000000000 : ℝ)^1689 := by
    have hnat : (1683200691 : ℕ)^2201*100000000000000^1689 ≤ 9807274316987^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683200691 10000000000 9807274316987 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259406671/10000000000 : ℝ), (139848147/250000000 : ℝ), (-1683200691/10000000000 : ℝ)] ![(2705341590473/6250000000000 : ℝ), (46907260217583/100000000000000 : ℝ), (9807274316987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259406671/10000000000 : ℝ)|^2201 ≤ (2705341590473/6250000000000 : ℝ)^1689
        have hw : |(5259406671/10000000000 : ℝ)|=(5259406671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(139848147/250000000 : ℝ)|^2201 ≤ (46907260217583/100000000000000 : ℝ)^1689
        have hw : |(139848147/250000000 : ℝ)|=(139848147/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1683200691/10000000000 : ℝ)|^2201 ≤ (9807274316987/100000000000000 : ℝ)^1689
        have hw : |(-1683200691/10000000000 : ℝ)|=(1683200691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s1_7 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4275099573/10000000000 : ℝ)*x 0 + (4859985697/10000000000 : ℝ)*x 1 + (1877613879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275099573/10000000000 : ℝ)^2201 ≤ (1321697362609/4000000000000 : ℝ)^1689 := by
    have hnat : (4275099573 : ℕ)^2201*4000000000000^1689 ≤ 1321697362609^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275099573 10000000000 1321697362609 4000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4859985697/10000000000 : ℝ)^2201 ≤ (39051899616947/100000000000000 : ℝ)^1689 := by
    have hnat : (4859985697 : ℕ)^2201*100000000000000^1689 ≤ 39051899616947^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4859985697 10000000000 39051899616947 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877613879/5000000000 : ℝ)^2201 ≤ (5581133259763/20000000000000 : ℝ)^1689 := by
    have hnat : (1877613879 : ℕ)^2201*20000000000000^1689 ≤ 5581133259763^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877613879 5000000000 5581133259763 20000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275099573/10000000000 : ℝ), (4859985697/10000000000 : ℝ), (1877613879/5000000000 : ℝ)] ![(1321697362609/4000000000000 : ℝ), (39051899616947/100000000000000 : ℝ), (5581133259763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275099573/10000000000 : ℝ)|^2201 ≤ (1321697362609/4000000000000 : ℝ)^1689
        have hw : |(4275099573/10000000000 : ℝ)|=(4275099573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4859985697/10000000000 : ℝ)|^2201 ≤ (39051899616947/100000000000000 : ℝ)^1689
        have hw : |(4859985697/10000000000 : ℝ)|=(4859985697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1877613879/5000000000 : ℝ)|^2201 ≤ (5581133259763/20000000000000 : ℝ)^1689
        have hw : |(1877613879/5000000000 : ℝ)|=(1877613879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1442_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3879/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2139/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2139/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2139/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2139/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2139/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2139/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2139/100000 : ℝ) ^ (4401/1024 : ℝ) ≤ (1665075076223/25000000000000000000 : ℝ) := by
    have hpowers : (2139/100000 : ℝ)^4401 ≤ (1665075076223/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2139 : ℕ)^4401*25000000000000000000^1024 ≤ 1665075076223^1024*100000^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2139 100000 1665075076223 25000000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2139/100000 : ℝ)) (X := (1665075076223/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26169/100000 : ℝ) ^ (4401/1024 : ℝ) ≤ (314583177591235921/100000000000000000000 : ℝ) := by
    have hpowers : (26169/100000 : ℝ)^4401 ≤ (314583177591235921/100000000000000000000 : ℝ)^1024 := by
      have hnat : (26169 : ℕ)^4401*100000000000000000000^1024 ≤ 314583177591235921^1024*100000^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26169 100000 314583177591235921 100000000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26169/100000 : ℝ)) (X := (314583177591235921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500001665075076223/12500000000000000000 : ℝ) ≤ (8000000247949/8000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (12500001665075076223/12500000000000000000 : ℝ)^1024 ≤ (8000000247949/8000000000000 : ℝ)^4401 := by
      have hnat : (12500001665075076223 : ℕ)^1024*8000000000000^4401 ≤ 8000000247949^4401*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500001665075076223 12500000000000000000 8000000247949 8000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (8000000247949/8000000000000 : ℝ)) (X := (12500001665075076223/12500000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100314589837891540813/100000000000000000000 : ℝ) ≤ (5003655440826781/5000000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (100314589837891540813/100000000000000000000 : ℝ)^1024 ≤ (5003655440826781/5000000000000000 : ℝ)^4401 := by
      have hnat : (100314589837891540813 : ℕ)^1024*5000000000000000^4401 ≤ 5003655440826781^4401*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100314589837891540813 100000000000000000000 5003655440826781 5000000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003655440826781/5000000000000000 : ℝ)) (X := (100314589837891540813/100000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50314583177591235921/50000000000000000000 : ℝ) ≤ (5007310726685437/5000000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (50314583177591235921/50000000000000000000 : ℝ)^1024 ≤ (5007310726685437/5000000000000000 : ℝ)^4401 := by
      have hnat : (50314583177591235921 : ℕ)^1024*5000000000000000^4401 ≤ 5007310726685437^4401*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50314583177591235921 50000000000000000000 5007310726685437 5000000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007310726685437/5000000000000000 : ℝ)) (X := (50314583177591235921/50000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1665075076223/25000000000000000000 : ℝ) ≤ ((2224710489092235433/2225000000000000000 : ℝ)+2*(4230654929/1390625000000 : ℝ)*(2139/100000 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (2224710489092235433/2225000000000000000 : ℝ)+2*(4230654929/1390625000000 : ℝ)*(2139/100000 : ℝ)=(8000000247949/8000000000000 : ℝ) by norm_num, show 1+2*(1665075076223/25000000000000000000 : ℝ)=(12500001665075076223/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(314583177591235921/100000000000000000000 : ℝ)+(1665075076223/25000000000000000000 : ℝ) ≤ ((2224710489092235433/2225000000000000000 : ℝ)+(4230654929/1390625000000 : ℝ)*((26169/100000 : ℝ)+(2139/100000 : ℝ)))^(4401/1024 : ℝ) := by
    rw [show (2224710489092235433/2225000000000000000 : ℝ)+(4230654929/1390625000000 : ℝ)*((26169/100000 : ℝ)+(2139/100000 : ℝ))=(5003655440826781/5000000000000000 : ℝ) by norm_num, show 1+(314583177591235921/100000000000000000000 : ℝ)+(1665075076223/25000000000000000000 : ℝ)=(100314589837891540813/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(314583177591235921/100000000000000000000 : ℝ) ≤ ((2224710489092235433/2225000000000000000 : ℝ)+2*(4230654929/1390625000000 : ℝ)*(26169/100000 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (2224710489092235433/2225000000000000000 : ℝ)+2*(4230654929/1390625000000 : ℝ)*(26169/100000 : ℝ)=(5007310726685437/5000000000000000 : ℝ) by norm_num, show 1+2*(314583177591235921/100000000000000000000 : ℝ)=(50314583177591235921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2224710489092235433/2225000000000000000 : ℝ)*(X 1 0+X 2 0)+(4230654929/1390625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (2139/100000 : ℝ)) (hi := (26169/100000 : ℝ)) (c := (2224710489092235433/2225000000000000000 : ℝ)) (alpha := (4230654929/1390625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2224710489092235433/2225000000000000000 : ℝ)*(X 0 1+X 2 1)+(4230654929/1390625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (2139/100000 : ℝ)) (hi := (26169/100000 : ℝ)) (c := (2224710489092235433/2225000000000000000 : ℝ)) (alpha := (4230654929/1390625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2224710489092235433/2225000000000000000 : ℝ)*(X 0 2+X 1 2)+(4230654929/1390625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (2139/100000 : ℝ)) (hi := (26169/100000 : ℝ)) (c := (2224710489092235433/2225000000000000000 : ℝ)) (alpha := (4230654929/1390625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-240248851/1250000000 : ℝ)*X 0 0+(2800034157/5000000000 : ℝ)*X 0 1+(1269908303/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5395511841/10000000000 : ℝ)*X 1 0+(-2197492187/10000000000 : ℝ)*X 1 1+(2539817377/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5395513091/10000000000 : ℝ)*X 2 0+(1269908337/2500000000 : ℝ)*X 2 1+(-1098746179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((267141967/625000000 : ℝ)*X 0 0+(1870939403/5000000000 : ℝ)*X 0 1+(1218278829/2500000000 : ℝ)*X 0 2+(267141967/625000000 : ℝ)*X 1 0+(1870939403/5000000000 : ℝ)*X 1 1+(1218278829/2500000000 : ℝ)*X 1 2+(267141967/625000000 : ℝ)*X 2 0+(1870939403/5000000000 : ℝ)*X 2 1+(1218278829/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1922371553/10000000000 : ℝ)*X 0 0+(203426969/400000000 : ℝ)*X 0 1+(699240737/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5259406749/10000000000 : ℝ)*X 1 0+(-1683200523/10000000000 : ℝ)*X 1 1+(34962037/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259406671/10000000000 : ℝ)*X 2 0+(139848147/250000000 : ℝ)*X 2 1+(-1683200691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4275099573/10000000000 : ℝ)*X 0 0+(4859985697/10000000000 : ℝ)*X 0 1+(1877613879/5000000000 : ℝ)*X 0 2+(4275099573/10000000000 : ℝ)*X 1 0+(4859985697/10000000000 : ℝ)*X 1 1+(1877613879/5000000000 : ℝ)*X 1 2+(4275099573/10000000000 : ℝ)*X 2 0+(4859985697/10000000000 : ℝ)*X 2 1+(1877613879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1690104161799563351314809/869140625000000000000000000000 : ℝ) := by norm_num
    linear_combination (223979671/100000000000000 : ℝ)*(base19) + (305910909/50000000000000 : ℝ)*(base23) + (255929/4000000000000 : ℝ)*(upper2) + (37322913/100000000000000 : ℝ)*(upper4) + (3855403/20000000000000 : ℝ)*(lower5) + (87671128542089/6250000000000 : ℝ)*(major0) + (87671128542089/6250000000000 : ℝ)*(major1) + (87671128542089/6250000000000 : ℝ)*(major2) + (480368932114803/25000000000000 : ℝ)*(sp0) + (120092713032423/6250000000000 : ℝ)*(sp1) + (96074151033831/5000000000000 : ℝ)*(sp2) + (883990085052157/100000000000000 : ℝ)*(sp3) + (7904039227/100000000000000 : ℝ)*(sp4) + (233097727/10000000000000 : ℝ)*(sp7) + (441996208014713/50000000000000 : ℝ)*(f.failure) + (1921483632498439/100000000000000 : ℝ)*(f.sum) + (5222514500403/2225000000000000000000000000 : ℝ)*base66 + (89809920912604213/13906250000000000000000000000000 : ℝ)*base68 + (69578332902760463/13906250000000000000000000000000 : ℝ)*base70 + (100151697647447963/13906250000000000000000000000000 : ℝ)*base72 + (200091103143/556250000000000000000000000 : ℝ)*base73 + (94837530481510463/13906250000000000000000000000000 : ℝ)*base76 + (14946720670572963/13906250000000000000000000000000 : ℝ)*base78 + (32975436991614537/13906250000000000000000000000000 : ℝ)*base79 + (516684890533/139062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13718319/5000000000000000000000 : ℝ)*base90 + (13718319/5000000000000000000000 : ℝ)*base92 + (13718319/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8802785225555526112591023/1112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61817557/100000000000000 : ℝ)*(base1) + (42263857/2500000000000 : ℝ)*(base19) + (1650582999/100000000000000 : ℝ)*(base23) + (97373411/50000000000000 : ℝ)*(upper3) + (513933/312500000000 : ℝ)*(upper5) + (14363523556577/1000000000000 : ℝ)*(major0) + (14363523556577/1000000000000 : ℝ)*(major1) + (14363523556577/1000000000000 : ℝ)*(major2) + (126452129/1250000000000 : ℝ)*(sp1) + (9699058821/100000000000000 : ℝ)*(sp2) + (983764338112109/50000000000000 : ℝ)*(sp4) + (1967516807682061/100000000000000 : ℝ)*(sp5) + (49187931619121/2500000000000 : ℝ)*(sp6) + (905175771337311/100000000000000 : ℝ)*(sp7) + (905175833154869/100000000000000 : ℝ)*(f.failure) + (98376430720333/5000000000000 : ℝ)*(f.sum) + (253377917463/89000000000000000000000000 : ℝ)*base65 + (6085269889567841/2225000000000000000000000000000 : ℝ)*base67 + (8650474014457159/2225000000000000000000000000000 : ℝ)*base70 + (8073373419307159/2225000000000000000000000000000 : ℝ)*base72 + (6453762017/1390625000000000000000000 : ℝ)*base73 + (5156496599657159/2225000000000000000000000000000 : ℝ)*base76 + (3677629025257159/2225000000000000000000000000000 : ℝ)*base78 + (14647423980517841/2225000000000000000000000000000 : ℝ)*base79 + (19104825399/22250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (64875053/10000000000000000000000 : ℝ)*base89 + (64875053/10000000000000000000000 : ℝ)*base91 + (64875053/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1442_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3879/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1442_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1442_s2_0 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-977082831/5000000000 : ℝ)*x 0 + (5455306743/10000000000 : ℝ)*x 1 + (130091743/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977082831/5000000000 : ℝ)^2201 ≤ (2978275513997/25000000000000 : ℝ)^1689 := by
    have hnat : (977082831 : ℕ)^2201*25000000000000^1689 ≤ 2978275513997^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977082831 5000000000 2978275513997 25000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455306743/10000000000 : ℝ)^2201 ≤ (2269912328077/5000000000000 : ℝ)^1689 := by
    have hnat : (5455306743 : ℕ)^2201*5000000000000^1689 ≤ 2269912328077^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455306743 10000000000 2269912328077 5000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130091743/250000000 : ℝ)^2201 ≤ (8537730273747/20000000000000 : ℝ)^1689 := by
    have hnat : (130091743 : ℕ)^2201*20000000000000^1689 ≤ 8537730273747^1689*250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130091743 250000000 8537730273747 20000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977082831/5000000000 : ℝ), (5455306743/10000000000 : ℝ), (130091743/250000000 : ℝ)] ![(2978275513997/25000000000000 : ℝ), (2269912328077/5000000000000 : ℝ), (8537730273747/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977082831/5000000000 : ℝ)|^2201 ≤ (2978275513997/25000000000000 : ℝ)^1689
        have hw : |(-977082831/5000000000 : ℝ)|=(977082831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455306743/10000000000 : ℝ)|^2201 ≤ (2269912328077/5000000000000 : ℝ)^1689
        have hw : |(5455306743/10000000000 : ℝ)|=(5455306743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130091743/250000000 : ℝ)|^2201 ≤ (8537730273747/20000000000000 : ℝ)^1689
        have hw : |(130091743/250000000 : ℝ)|=(130091743/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s2_1 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2679662221/5000000000 : ℝ)*x 0 + (-1041779477/5000000000 : ℝ)*x 1 + (1300917377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679662221/5000000000 : ℝ)^2201 ≤ (22180075934651/50000000000000 : ℝ)^1689 := by
    have hnat : (2679662221 : ℕ)^2201*50000000000000^1689 ≤ 22180075934651^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679662221 5000000000 22180075934651 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041779477/5000000000 : ℝ)^2201 ≤ (12951199011153/100000000000000 : ℝ)^1689 := by
    have hnat : (1041779477 : ℕ)^2201*100000000000000^1689 ≤ 12951199011153^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041779477 5000000000 12951199011153 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300917377/2500000000 : ℝ)^2201 ≤ (21344324551187/50000000000000 : ℝ)^1689 := by
    have hnat : (1300917377 : ℕ)^2201*50000000000000^1689 ≤ 21344324551187^1689*2500000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300917377 2500000000 21344324551187 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679662221/5000000000 : ℝ), (-1041779477/5000000000 : ℝ), (1300917377/2500000000 : ℝ)] ![(22180075934651/50000000000000 : ℝ), (12951199011153/100000000000000 : ℝ), (21344324551187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679662221/5000000000 : ℝ)|^2201 ≤ (22180075934651/50000000000000 : ℝ)^1689
        have hw : |(2679662221/5000000000 : ℝ)|=(2679662221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1041779477/5000000000 : ℝ)|^2201 ≤ (12951199011153/100000000000000 : ℝ)^1689
        have hw : |(-1041779477/5000000000 : ℝ)|=(1041779477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300917377/2500000000 : ℝ)|^2201 ≤ (21344324551187/50000000000000 : ℝ)^1689
        have hw : |(1300917377/2500000000 : ℝ)|=(1300917377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s2_2 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2679661967/5000000000 : ℝ)*x 0 + (5203670027/10000000000 : ℝ)*x 1 + (-1041779473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679661967/5000000000 : ℝ)^2201 ≤ (44360146389851/100000000000000 : ℝ)^1689 := by
    have hnat : (2679661967 : ℕ)^2201*100000000000000^1689 ≤ 44360146389851^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679661967 5000000000 44360146389851 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5203670027/10000000000 : ℝ)^2201 ≤ (42688654650681/100000000000000 : ℝ)^1689 := by
    have hnat : (5203670027 : ℕ)^2201*100000000000000^1689 ≤ 42688654650681^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203670027 10000000000 42688654650681 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041779473/5000000000 : ℝ)^2201 ≤ (809449934147/6250000000000 : ℝ)^1689 := by
    have hnat : (1041779473 : ℕ)^2201*6250000000000^1689 ≤ 809449934147^1689*5000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041779473 5000000000 809449934147 6250000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679661967/5000000000 : ℝ), (5203670027/10000000000 : ℝ), (-1041779473/5000000000 : ℝ)] ![(44360146389851/100000000000000 : ℝ), (42688654650681/100000000000000 : ℝ), (809449934147/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679661967/5000000000 : ℝ)|^2201 ≤ (44360146389851/100000000000000 : ℝ)^1689
        have hw : |(2679661967/5000000000 : ℝ)|=(2679661967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5203670027/10000000000 : ℝ)|^2201 ≤ (42688654650681/100000000000000 : ℝ)^1689
        have hw : |(5203670027/10000000000 : ℝ)|=(5203670027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1041779473/5000000000 : ℝ)|^2201 ≤ (809449934147/6250000000000 : ℝ)^1689
        have hw : |(-1041779473/5000000000 : ℝ)|=(1041779473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s2_3 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (107425391/250000000 : ℝ)*x 0 + (4031299761/10000000000 : ℝ)*x 1 + (4578269689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107425391/250000000 : ℝ)^2201 ≤ (16631672122613/50000000000000 : ℝ)^1689 := by
    have hnat : (107425391 : ℕ)^2201*50000000000000^1689 ≤ 16631672122613^1689*250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107425391 250000000 16631672122613 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4031299761/10000000000 : ℝ)^2201 ≤ (1224335713231/4000000000000 : ℝ)^1689 := by
    have hnat : (4031299761 : ℕ)^2201*4000000000000^1689 ≤ 1224335713231^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031299761 10000000000 1224335713231 4000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4578269689/10000000000 : ℝ)^2201 ≤ (18064131455763/50000000000000 : ℝ)^1689 := by
    have hnat : (4578269689 : ℕ)^2201*50000000000000^1689 ≤ 18064131455763^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578269689 10000000000 18064131455763 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107425391/250000000 : ℝ), (4031299761/10000000000 : ℝ), (4578269689/10000000000 : ℝ)] ![(16631672122613/50000000000000 : ℝ), (1224335713231/4000000000000 : ℝ), (18064131455763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107425391/250000000 : ℝ)|^2201 ≤ (16631672122613/50000000000000 : ℝ)^1689
        have hw : |(107425391/250000000 : ℝ)|=(107425391/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4031299761/10000000000 : ℝ)|^2201 ≤ (1224335713231/4000000000000 : ℝ)^1689
        have hw : |(4031299761/10000000000 : ℝ)|=(4031299761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4578269689/10000000000 : ℝ)|^2201 ≤ (18064131455763/50000000000000 : ℝ)^1689
        have hw : |(4578269689/10000000000 : ℝ)|=(4578269689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s2_4 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1954208597/10000000000 : ℝ)*x 0 + (162659101/312500000 : ℝ)*x 1 + (5453873869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1954208597/10000000000 : ℝ)^2201 ≤ (11913443144263/100000000000000 : ℝ)^1689 := by
    have hnat : (1954208597 : ℕ)^2201*100000000000000^1689 ≤ 11913443144263^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954208597 10000000000 11913443144263 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162659101/312500000 : ℝ)^2201 ≤ (4270384849999/10000000000000 : ℝ)^1689 := by
    have hnat : (162659101 : ℕ)^2201*10000000000000^1689 ≤ 4270384849999^1689*312500000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162659101 312500000 4270384849999 10000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453873869/10000000000 : ℝ)^2201 ≤ (45382708350767/100000000000000 : ℝ)^1689 := by
    have hnat : (5453873869 : ℕ)^2201*100000000000000^1689 ≤ 45382708350767^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453873869 10000000000 45382708350767 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1954208597/10000000000 : ℝ), (162659101/312500000 : ℝ), (5453873869/10000000000 : ℝ)] ![(11913443144263/100000000000000 : ℝ), (4270384849999/10000000000000 : ℝ), (45382708350767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1954208597/10000000000 : ℝ)|^2201 ≤ (11913443144263/100000000000000 : ℝ)^1689
        have hw : |(-1954208597/10000000000 : ℝ)|=(1954208597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162659101/312500000 : ℝ)|^2201 ≤ (4270384849999/10000000000000 : ℝ)^1689
        have hw : |(162659101/312500000 : ℝ)|=(162659101/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453873869/10000000000 : ℝ)|^2201 ≤ (45382708350767/100000000000000 : ℝ)^1689
        have hw : |(5453873869/10000000000 : ℝ)|=(5453873869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s2_5 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (661726373/1250000000 : ℝ)*x 0 + (-1833353679/10000000000 : ℝ)*x 1 + (5453874849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661726373/1250000000 : ℝ)^2201 ≤ (4365481566041/10000000000000 : ℝ)^1689 := by
    have hnat : (661726373 : ℕ)^2201*10000000000000^1689 ≤ 4365481566041^1689*1250000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661726373 1250000000 4365481566041 10000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1833353679/10000000000 : ℝ)^2201 ≤ (10962465338837/100000000000000 : ℝ)^1689 := by
    have hnat : (1833353679 : ℕ)^2201*100000000000000^1689 ≤ 10962465338837^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833353679 10000000000 10962465338837 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453874849/10000000000 : ℝ)^2201 ≤ (45382718977549/100000000000000 : ℝ)^1689 := by
    have hnat : (5453874849 : ℕ)^2201*100000000000000^1689 ≤ 45382718977549^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453874849 10000000000 45382718977549 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661726373/1250000000 : ℝ), (-1833353679/10000000000 : ℝ), (5453874849/10000000000 : ℝ)] ![(4365481566041/10000000000000 : ℝ), (10962465338837/100000000000000 : ℝ), (45382718977549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661726373/1250000000 : ℝ)|^2201 ≤ (4365481566041/10000000000000 : ℝ)^1689
        have hw : |(661726373/1250000000 : ℝ)|=(661726373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1833353679/10000000000 : ℝ)|^2201 ≤ (10962465338837/100000000000000 : ℝ)^1689
        have hw : |(-1833353679/10000000000 : ℝ)|=(1833353679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453874849/10000000000 : ℝ)|^2201 ≤ (45382718977549/100000000000000 : ℝ)^1689
        have hw : |(5453874849/10000000000 : ℝ)|=(5453874849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s2_6 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1058762083/2000000000 : ℝ)*x 0 + (5453874721/10000000000 : ℝ)*x 1 + (-1833354643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058762083/2000000000 : ℝ)^2201 ≤ (43654809545833/100000000000000 : ℝ)^1689 := by
    have hnat : (1058762083 : ℕ)^2201*100000000000000^1689 ≤ 43654809545833^1689*2000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058762083 2000000000 43654809545833 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453874721/10000000000 : ℝ)^2201 ≤ (45382717589561/100000000000000 : ℝ)^1689 := by
    have hnat : (5453874721 : ℕ)^2201*100000000000000^1689 ≤ 45382717589561^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453874721 10000000000 45382717589561 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833354643/10000000000 : ℝ)^2201 ≤ (685154553149/6250000000000 : ℝ)^1689 := by
    have hnat : (1833354643 : ℕ)^2201*6250000000000^1689 ≤ 685154553149^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833354643 10000000000 685154553149 6250000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058762083/2000000000 : ℝ), (5453874721/10000000000 : ℝ), (-1833354643/10000000000 : ℝ)] ![(43654809545833/100000000000000 : ℝ), (45382717589561/100000000000000 : ℝ), (685154553149/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058762083/2000000000 : ℝ)|^2201 ≤ (43654809545833/100000000000000 : ℝ)^1689
        have hw : |(1058762083/2000000000 : ℝ)|=(1058762083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453874721/10000000000 : ℝ)|^2201 ≤ (45382717589561/100000000000000 : ℝ)^1689
        have hw : |(5453874721/10000000000 : ℝ)|=(5453874721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1833354643/10000000000 : ℝ)|^2201 ≤ (685154553149/6250000000000 : ℝ)^1689
        have hw : |(-1833354643/10000000000 : ℝ)|=(1833354643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1442_s2_7 (p : ℝ) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4297109337/10000000000 : ℝ)*x 0 + (4575181071/10000000000 : ℝ)*x 1 + (403441361/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297109337/10000000000 : ℝ)^2201 ≤ (16632144714753/50000000000000 : ℝ)^1689 := by
    have hnat : (4297109337 : ℕ)^2201*50000000000000^1689 ≤ 16632144714753^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297109337 10000000000 16632144714753 50000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4575181071/10000000000 : ℝ)^2201 ≤ (28877203769/80000000000 : ℝ)^1689 := by
    have hnat : (4575181071 : ℕ)^2201*80000000000^1689 ≤ 28877203769^1689*10000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575181071 10000000000 28877203769 80000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403441361/1000000000 : ℝ)^2201 ≤ (30639205846667/100000000000000 : ℝ)^1689 := by
    have hnat : (403441361 : ℕ)^2201*100000000000000^1689 ≤ 30639205846667^1689*1000000000^2201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403441361 1000000000 30639205846667 100000000000000 2201 1689 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2201/512 : ℝ)) 2201 1689 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297109337/10000000000 : ℝ), (4575181071/10000000000 : ℝ), (403441361/1000000000 : ℝ)] ![(16632144714753/50000000000000 : ℝ), (28877203769/80000000000 : ℝ), (30639205846667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297109337/10000000000 : ℝ)|^2201 ≤ (16632144714753/50000000000000 : ℝ)^1689
        have hw : |(4297109337/10000000000 : ℝ)|=(4297109337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4575181071/10000000000 : ℝ)|^2201 ≤ (28877203769/80000000000 : ℝ)^1689
        have hw : |(4575181071/10000000000 : ℝ)|=(4575181071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403441361/1000000000 : ℝ)|^2201 ≤ (30639205846667/100000000000000 : ℝ)^1689
        have hw : |(403441361/1000000000 : ℝ)|=(403441361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1442_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3879/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2609/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3879/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3879/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3879/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3879/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3879/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3879/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3879/50000 : ℝ) ^ (4401/1024 : ℝ) ≤ (1691645418398219/100000000000000000000 : ℝ) := by
    have hpowers : (3879/50000 : ℝ)^4401 ≤ (1691645418398219/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3879 : ℕ)^4401*100000000000000000000^1024 ≤ 1691645418398219^1024*50000^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3879 50000 1691645418398219 100000000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3879/50000 : ℝ)) (X := (1691645418398219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18761/100000 : ℝ) ^ (4401/1024 : ℝ) ≤ (18814908109973171/25000000000000000000 : ℝ) := by
    have hpowers : (18761/100000 : ℝ)^4401 ≤ (18814908109973171/25000000000000000000 : ℝ)^1024 := by
      have hnat : (18761 : ℕ)^4401*25000000000000000000^1024 ≤ 18814908109973171^1024*100000^4401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18761 100000 18814908109973171 25000000000000000000 4401 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18761/100000 : ℝ)) (X := (18814908109973171/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001691645418398219/50000000000000000000 : ℝ) ≤ (5000039359746049/5000000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (50001691645418398219/50000000000000000000 : ℝ)^1024 ≤ (5000039359746049/5000000000000000 : ℝ)^4401 := by
      have hnat : (50001691645418398219 : ℕ)^1024*5000000000000000^4401 ≤ 5000039359746049^4401*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001691645418398219 50000000000000000000 5000039359746049 5000000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000039359746049/5000000000000000 : ℝ)) (X := (50001691645418398219/50000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100076951277858290903/100000000000000000000 : ℝ) ≤ (250044748270411/250000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (100076951277858290903/100000000000000000000 : ℝ)^1024 ≤ (250044748270411/250000000000000 : ℝ)^4401 := by
      have hnat : (100076951277858290903 : ℕ)^1024*250000000000000^4401 ≤ 250044748270411^4401*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100076951277858290903 100000000000000000000 250044748270411 250000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250044748270411/250000000000000 : ℝ)) (X := (100076951277858290903/100000000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12518814908109973171/12500000000000000000 : ℝ) ≤ (5001750571070391/5000000000000000 : ℝ) ^ (4401/1024 : ℝ) := by
    have hpowers : (12518814908109973171/12500000000000000000 : ℝ)^1024 ≤ (5001750571070391/5000000000000000 : ℝ)^4401 := by
      have hnat : (12518814908109973171 : ℕ)^1024*5000000000000000^4401 ≤ 5001750571070391^4401*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518814908109973171 12500000000000000000 5001750571070391 5000000000000000 1024 4401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001750571070391/5000000000000000 : ℝ)) (X := (12518814908109973171/12500000000000000000 : ℝ)) (by norm_num) 4401 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1691645418398219/100000000000000000000 : ℝ) ≤ ((55002157497831531911/55015000000000000000 : ℝ)+2*(855605662171/550150000000000 : ℝ)*(3879/50000 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (55002157497831531911/55015000000000000000 : ℝ)+2*(855605662171/550150000000000 : ℝ)*(3879/50000 : ℝ)=(5000039359746049/5000000000000000 : ℝ) by norm_num, show 1+2*(1691645418398219/100000000000000000000 : ℝ)=(50001691645418398219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18814908109973171/25000000000000000000 : ℝ)+(1691645418398219/100000000000000000000 : ℝ) ≤ ((55002157497831531911/55015000000000000000 : ℝ)+(855605662171/550150000000000 : ℝ)*((18761/100000 : ℝ)+(3879/50000 : ℝ)))^(4401/1024 : ℝ) := by
    rw [show (55002157497831531911/55015000000000000000 : ℝ)+(855605662171/550150000000000 : ℝ)*((18761/100000 : ℝ)+(3879/50000 : ℝ))=(250044748270411/250000000000000 : ℝ) by norm_num, show 1+(18814908109973171/25000000000000000000 : ℝ)+(1691645418398219/100000000000000000000 : ℝ)=(100076951277858290903/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18814908109973171/25000000000000000000 : ℝ) ≤ ((55002157497831531911/55015000000000000000 : ℝ)+2*(855605662171/550150000000000 : ℝ)*(18761/100000 : ℝ))^(4401/1024 : ℝ) := by
    rw [show (55002157497831531911/55015000000000000000 : ℝ)+2*(855605662171/550150000000000 : ℝ)*(18761/100000 : ℝ)=(5001750571070391/5000000000000000 : ℝ) by norm_num, show 1+2*(18814908109973171/25000000000000000000 : ℝ)=(12518814908109973171/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55002157497831531911/55015000000000000000 : ℝ)*(X 1 0+X 2 0)+(855605662171/550150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (3879/50000 : ℝ)) (hi := (18761/100000 : ℝ)) (c := (55002157497831531911/55015000000000000000 : ℝ)) (alpha := (855605662171/550150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55002157497831531911/55015000000000000000 : ℝ)*(X 0 1+X 2 1)+(855605662171/550150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (3879/50000 : ℝ)) (hi := (18761/100000 : ℝ)) (c := (55002157497831531911/55015000000000000000 : ℝ)) (alpha := (855605662171/550150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55002157497831531911/55015000000000000000 : ℝ)*(X 0 2+X 1 2)+(855605662171/550150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4401/1024 : ℝ)) (lo := (3879/50000 : ℝ)) (hi := (18761/100000 : ℝ)) (c := (55002157497831531911/55015000000000000000 : ℝ)) (alpha := (855605662171/550150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-977082831/5000000000 : ℝ)*X 0 0+(5455306743/10000000000 : ℝ)*X 0 1+(130091743/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679662221/5000000000 : ℝ)*X 1 0+(-1041779477/5000000000 : ℝ)*X 1 1+(1300917377/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679661967/5000000000 : ℝ)*X 2 0+(5203670027/10000000000 : ℝ)*X 2 1+(-1041779473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107425391/250000000 : ℝ)*X 0 0+(4031299761/10000000000 : ℝ)*X 0 1+(4578269689/10000000000 : ℝ)*X 0 2+(107425391/250000000 : ℝ)*X 1 0+(4031299761/10000000000 : ℝ)*X 1 1+(4578269689/10000000000 : ℝ)*X 1 2+(107425391/250000000 : ℝ)*X 2 0+(4031299761/10000000000 : ℝ)*X 2 1+(4578269689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1954208597/10000000000 : ℝ)*X 0 0+(162659101/312500000 : ℝ)*X 0 1+(5453873869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661726373/1250000000 : ℝ)*X 1 0+(-1833353679/10000000000 : ℝ)*X 1 1+(5453874849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058762083/2000000000 : ℝ)*X 2 0+(5453874721/10000000000 : ℝ)*X 2 1+(-1833354643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4297109337/10000000000 : ℝ)*X 0 0+(4575181071/10000000000 : ℝ)*X 0 1+(403441361/1000000000 : ℝ)*X 0 2+(4297109337/10000000000 : ℝ)*X 1 0+(4575181071/10000000000 : ℝ)*X 1 1+(403441361/1000000000 : ℝ)*X 1 2+(4297109337/10000000000 : ℝ)*X 2 0+(4575181071/10000000000 : ℝ)*X 2 1+(403441361/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1442_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8231970379620541536512072547/1375375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140456251/20000000000000 : ℝ)*(base19) + (22344149/20000000000000 : ℝ)*(base23) + (116118127/100000000000000 : ℝ)*(lower2) + (14461779/6250000000000 : ℝ)*(upper3) + (299213/20000000000000 : ℝ)*(lower4) + (1450561738127841/50000000000000 : ℝ)*(major0) + (1450561738127841/50000000000000 : ℝ)*(major1) + (1450561738127841/50000000000000 : ℝ)*(major2) + (397398499925323/10000000000000 : ℝ)*(sp0) + (993496286073373/25000000000000 : ℝ)*(sp1) + (3973985734854003/100000000000000 : ℝ)*(sp2) + (1828256446194287/100000000000000 : ℝ)*(sp3) + (423660759/50000000000000 : ℝ)*(sp4) + (2230116907/50000000000000 : ℝ)*(sp7) + (914130453214051/50000000000000 : ℝ)*(f.failure) + (993496461643687/25000000000000 : ℝ)*(f.sum) + (27313174811179/3438437500000000000000000000 : ℝ)*base65 + (9509159316980115849/2750750000000000000000000000000000 : ℝ)*base68 + (9205227880701384151/2750750000000000000000000000000000 : ℝ)*base69 + (7707121465873634151/2750750000000000000000000000000000 : ℝ)*base71 + (168747680503749/55015000000000000000000000000 : ℝ)*base73 + (27639562772305884151/2750750000000000000000000000000000 : ℝ)*base75 + (13684020820879865849/2750750000000000000000000000000000 : ℝ)*base78 + (4184602285758634151/2750750000000000000000000000000000 : ℝ)*base79 + (428570233219569/55015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (31106987/5000000000000000000000 : ℝ)*base89 + (31106987/5000000000000000000000 : ℝ)*base91 + (31106987/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7581678456558542123860949799/550150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1201164783/100000000000000 : ℝ)*(base19) + (298098899/25000000000000 : ℝ)*(base23) + (219534467/50000000000000 : ℝ)*(upper3) + (464817/195312500000 : ℝ)*(lower4) + (586878172267401/20000000000000 : ℝ)*(major0) + (586878172267401/20000000000000 : ℝ)*(major1) + (586878172267401/20000000000000 : ℝ)*(major2) + (10010019217/50000000000000 : ℝ)*(sp1) + (17895893047/100000000000000 : ℝ)*(sp2) + (25855241/50000000000000 : ℝ)*(sp3) + (1004888890412533/25000000000000 : ℝ)*(sp4) + (803906868089383/20000000000000 : ℝ)*(sp5) + (401953647336149/10000000000000 : ℝ)*(sp6) + (184922564994301/10000000000000 : ℝ)*(sp7) + (462306425413373/25000000000000 : ℝ)*(f.failure) + (1004888890412533/25000000000000 : ℝ)*(f.sum) + (11618789211249/2750750000000000000000000000 : ℝ)*base66 + (4047254835027166689/1100300000000000000000000000000000 : ℝ)*base68 + (3975675665758166689/1100300000000000000000000000000000 : ℝ)*base70 + (3112373829197766689/1100300000000000000000000000000000 : ℝ)*base72 + (6534620536431/11003000000000000000000000000 : ℝ)*base74 + (1441476367837866689/1100300000000000000000000000000000 : ℝ)*base76 + (13787140101315766689/1100300000000000000000000000000000 : ℝ)*base78 + (1574499959707666689/1100300000000000000000000000000000 : ℝ)*base80 + (1154360460933/343843750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (11018101/2500000000000000000000 : ℝ)*base89 + (11018101/2500000000000000000000 : ℝ)*base91 + (11018101/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1442_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3879/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1442_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1442_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15761/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1442_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1442_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1442_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4401/1024 : ℝ) ≤ p) (hpb : p ≤ (2201/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158682137/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15761/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1442_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

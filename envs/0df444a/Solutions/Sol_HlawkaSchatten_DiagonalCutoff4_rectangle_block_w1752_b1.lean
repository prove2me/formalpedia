-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1752_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:19:35.431771+00:00
-- url     : https://prove2.me/submissions/0d25b196-cae4-4e6c-9b85-05de265313e7

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
theorem support_rectangle_w1752_s3_0 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2667441017/5000000000 : ℝ)*x 0 + (2540851947/5000000000 : ℝ)*x 1 + (-285374101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2667441017/5000000000 : ℝ)^5807 ≤ (1457318793581/3125000000000 : ℝ)^4783 := by
    have hnat : (2667441017 : ℕ)^5807*3125000000000^4783 ≤ 1457318793581^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667441017 5000000000 1457318793581 3125000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540851947/5000000000 : ℝ)^5807 ≤ (21980544167523/50000000000000 : ℝ)^4783 := by
    have hnat : (2540851947 : ℕ)^5807*50000000000000^4783 ≤ 21980544167523^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540851947 5000000000 21980544167523 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285374101/2000000000 : ℝ)^5807 ≤ (1175588781589/12500000000000 : ℝ)^4783 := by
    have hnat : (285374101 : ℕ)^5807*12500000000000^4783 ≤ 1175588781589^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285374101 2000000000 1175588781589 12500000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2667441017/5000000000 : ℝ), (2540851947/5000000000 : ℝ), (-285374101/2000000000 : ℝ)] ![(1457318793581/3125000000000 : ℝ), (21980544167523/50000000000000 : ℝ), (1175588781589/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2667441017/5000000000 : ℝ)|^5807 ≤ (1457318793581/3125000000000 : ℝ)^4783
        have hw : |(2667441017/5000000000 : ℝ)|=(2667441017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540851947/5000000000 : ℝ)|^5807 ≤ (21980544167523/50000000000000 : ℝ)^4783
        have hw : |(2540851947/5000000000 : ℝ)|=(2540851947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-285374101/2000000000 : ℝ)|^5807 ≤ (1175588781589/12500000000000 : ℝ)^4783
        have hw : |(-285374101/2000000000 : ℝ)|=(285374101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s3_1 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1211446953/10000000000 : ℝ)*x 0 + (2544218499/5000000000 : ℝ)*x 1 + (5487450503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1211446953/10000000000 : ℝ)^5807 ≤ (7709879638367/100000000000000 : ℝ)^4783 := by
    have hnat : (1211446953 : ℕ)^5807*100000000000000^4783 ≤ 7709879638367^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211446953 10000000000 7709879638367 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544218499/5000000000 : ℝ)^5807 ≤ (8806363138081/20000000000000 : ℝ)^4783 := by
    have hnat : (2544218499 : ℕ)^5807*20000000000000^4783 ≤ 8806363138081^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544218499 5000000000 8806363138081 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487450503/10000000000 : ℝ)^5807 ≤ (4825830465091/10000000000000 : ℝ)^4783 := by
    have hnat : (5487450503 : ℕ)^5807*10000000000000^4783 ≤ 4825830465091^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487450503 10000000000 4825830465091 10000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1211446953/10000000000 : ℝ), (2544218499/5000000000 : ℝ), (5487450503/10000000000 : ℝ)] ![(7709879638367/100000000000000 : ℝ), (8806363138081/20000000000000 : ℝ), (4825830465091/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1211446953/10000000000 : ℝ)|^5807 ≤ (7709879638367/100000000000000 : ℝ)^4783
        have hw : |(-1211446953/10000000000 : ℝ)|=(1211446953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544218499/5000000000 : ℝ)|^5807 ≤ (8806363138081/20000000000000 : ℝ)^4783
        have hw : |(2544218499/5000000000 : ℝ)|=(2544218499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487450503/10000000000 : ℝ)|^5807 ≤ (4825830465091/10000000000000 : ℝ)^4783
        have hw : |(5487450503/10000000000 : ℝ)|=(5487450503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s3_2 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225561789/10000000000 : ℝ)*x 0 + (-102112351/1000000000 : ℝ)*x 1 + (1371862613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225561789/10000000000 : ℝ)^5807 ≤ (45476563049123/100000000000000 : ℝ)^4783 := by
    have hnat : (5225561789 : ℕ)^5807*100000000000000^4783 ≤ 45476563049123^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225561789 10000000000 45476563049123 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102112351/1000000000 : ℝ)^5807 ≤ (1566283208169/25000000000000 : ℝ)^4783 := by
    have hnat : (102112351 : ℕ)^5807*25000000000000^4783 ≤ 1566283208169^4783*1000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102112351 1000000000 1566283208169 25000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371862613/2500000000 : ℝ)^5807 ≤ (24129152053189/50000000000000 : ℝ)^4783 := by
    have hnat : (1371862613 : ℕ)^5807*50000000000000^4783 ≤ 24129152053189^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371862613 2500000000 24129152053189 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225561789/10000000000 : ℝ), (-102112351/1000000000 : ℝ), (1371862613/2500000000 : ℝ)] ![(45476563049123/100000000000000 : ℝ), (1566283208169/25000000000000 : ℝ), (24129152053189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225561789/10000000000 : ℝ)|^5807 ≤ (45476563049123/100000000000000 : ℝ)^4783
        have hw : |(5225561789/10000000000 : ℝ)|=(5225561789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102112351/1000000000 : ℝ)|^5807 ≤ (1566283208169/25000000000000 : ℝ)^4783
        have hw : |(-102112351/1000000000 : ℝ)|=(102112351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1371862613/2500000000 : ℝ)|^5807 ≤ (24129152053189/50000000000000 : ℝ)^4783
        have hw : |(1371862613/2500000000 : ℝ)|=(1371862613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s3_3 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225561203/10000000000 : ℝ)*x 0 + (5487451077/10000000000 : ℝ)*x 1 + (-204224689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225561203/10000000000 : ℝ)^5807 ≤ (5684569607189/12500000000000 : ℝ)^4783 := by
    have hnat : (5225561203 : ℕ)^5807*12500000000000^4783 ≤ 5684569607189^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225561203 10000000000 5684569607189 12500000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487451077/10000000000 : ℝ)^5807 ≤ (48258310779559/100000000000000 : ℝ)^4783 := by
    have hnat : (5487451077 : ℕ)^5807*100000000000000^4783 ≤ 48258310779559^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487451077 10000000000 48258310779559 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204224689/2000000000 : ℝ)^5807 ≤ (1253026469697/20000000000000 : ℝ)^4783 := by
    have hnat : (204224689 : ℕ)^5807*20000000000000^4783 ≤ 1253026469697^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204224689 2000000000 1253026469697 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225561203/10000000000 : ℝ), (5487451077/10000000000 : ℝ), (-204224689/2000000000 : ℝ)] ![(5684569607189/12500000000000 : ℝ), (48258310779559/100000000000000 : ℝ), (1253026469697/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225561203/10000000000 : ℝ)|^5807 ≤ (5684569607189/12500000000000 : ℝ)^4783
        have hw : |(5225561203/10000000000 : ℝ)|=(5225561203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487451077/10000000000 : ℝ)|^5807 ≤ (48258310779559/100000000000000 : ℝ)^4783
        have hw : |(5487451077/10000000000 : ℝ)|=(5487451077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-204224689/2000000000 : ℝ)|^5807 ≤ (1253026469697/20000000000000 : ℝ)^4783
        have hw : |(-204224689/2000000000 : ℝ)|=(204224689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_s3_4 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4017877211/10000000000 : ℝ)*x 0 + (1177286361/2500000000 : ℝ)*x 1 + (169372341/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4017877211/10000000000 : ℝ)^5807 ≤ (33053365182557/100000000000000 : ℝ)^4783 := by
    have hnat : (4017877211 : ℕ)^5807*100000000000000^4783 ≤ 33053365182557^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017877211 10000000000 33053365182557 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1177286361/2500000000 : ℝ)^5807 ≤ (2504965688387/6250000000000 : ℝ)^4783 := by
    have hnat : (1177286361 : ℕ)^5807*6250000000000^4783 ≤ 2504965688387^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177286361 2500000000 2504965688387 6250000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169372341/500000000 : ℝ)^5807 ≤ (1343359189661/5000000000000 : ℝ)^4783 := by
    have hnat : (169372341 : ℕ)^5807*5000000000000^4783 ≤ 1343359189661^4783*500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169372341 500000000 1343359189661 5000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4017877211/10000000000 : ℝ), (1177286361/2500000000 : ℝ), (169372341/500000000 : ℝ)] ![(33053365182557/100000000000000 : ℝ), (2504965688387/6250000000000 : ℝ), (1343359189661/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4017877211/10000000000 : ℝ)|^5807 ≤ (33053365182557/100000000000000 : ℝ)^4783
        have hw : |(4017877211/10000000000 : ℝ)|=(4017877211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1177286361/2500000000 : ℝ)|^5807 ≤ (2504965688387/6250000000000 : ℝ)^4783
        have hw : |(1177286361/2500000000 : ℝ)|=(1177286361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169372341/500000000 : ℝ)|^5807 ≤ (1343359189661/5000000000000 : ℝ)^4783
        have hw : |(169372341/500000000 : ℝ)|=(169372341/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1752_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1813/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1813/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1121/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1813/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1813/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1813/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1813/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1813/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1813/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1813/20000 : ℝ) ^ (5791/1024 : ℝ) ≤ (126949168877627/100000000000000000000 : ℝ) := by
    have hpowers : (1813/20000 : ℝ)^5791 ≤ (126949168877627/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1813 : ℕ)^5791*100000000000000000000^1024 ≤ 126949168877627^1024*20000^5791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1813 20000 126949168877627 100000000000000000000 5791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1813/20000 : ℝ)) (X := (126949168877627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17937/100000 : ℝ) ^ (5791/1024 : ℝ) ≤ (3011071835002209/50000000000000000000 : ℝ) := by
    have hpowers : (17937/100000 : ℝ)^5791 ≤ (3011071835002209/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17937 : ℕ)^5791*50000000000000000000^1024 ≤ 3011071835002209^1024*100000^5791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17937 100000 3011071835002209 50000000000000000000 5791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17937/100000 : ℝ)) (X := (3011071835002209/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000126949168877627/50000000000000000000 : ℝ) ≤ (2500001122395209/2500000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (50000126949168877627/50000000000000000000 : ℝ)^1024 ≤ (2500001122395209/2500000000000000 : ℝ)^5791 := by
      have hnat : (50000126949168877627 : ℕ)^1024*2500000000000000^5791 ≤ 2500001122395209^5791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000126949168877627 50000000000000000000 2500001122395209 2500000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500001122395209/2500000000000000 : ℝ)) (X := (50000126949168877627/50000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20001229818567776409/20000000000000000000 : ℝ) ≤ (10000108729264573/10000000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (20001229818567776409/20000000000000000000 : ℝ)^1024 ≤ (10000108729264573/10000000000000000 : ℝ)^5791 := by
      have hnat : (20001229818567776409 : ℕ)^1024*10000000000000000^5791 ≤ 10000108729264573^5791*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20001229818567776409 20000000000000000000 10000108729264573 10000000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000108729264573/10000000000000000 : ℝ)) (X := (20001229818567776409/20000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25003011071835002209/25000000000000000000 : ℝ) ≤ (1000021296894831/1000000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (25003011071835002209/25000000000000000000 : ℝ)^1024 ≤ (1000021296894831/1000000000000000 : ℝ)^5791 := by
      have hnat : (25003011071835002209 : ℕ)^1024*1000000000000000^5791 ≤ 1000021296894831^5791*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003011071835002209 25000000000000000000 1000021296894831 1000000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000021296894831/1000000000000000 : ℝ)) (X := (25003011071835002209/25000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(126949168877627/100000000000000000000 : ℝ) ≤ ((44359074983047512591/44360000000000000000 : ℝ)+2*(104239683737/887200000000000 : ℝ)*(1813/20000 : ℝ))^(5791/1024 : ℝ) := by
    rw [show (44359074983047512591/44360000000000000000 : ℝ)+2*(104239683737/887200000000000 : ℝ)*(1813/20000 : ℝ)=(2500001122395209/2500000000000000 : ℝ) by norm_num, show 1+2*(126949168877627/100000000000000000000 : ℝ)=(50000126949168877627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3011071835002209/50000000000000000000 : ℝ)+(126949168877627/100000000000000000000 : ℝ) ≤ ((44359074983047512591/44360000000000000000 : ℝ)+(104239683737/887200000000000 : ℝ)*((17937/100000 : ℝ)+(1813/20000 : ℝ)))^(5791/1024 : ℝ) := by
    rw [show (44359074983047512591/44360000000000000000 : ℝ)+(104239683737/887200000000000 : ℝ)*((17937/100000 : ℝ)+(1813/20000 : ℝ))=(10000108729264573/10000000000000000 : ℝ) by norm_num, show 1+(3011071835002209/50000000000000000000 : ℝ)+(126949168877627/100000000000000000000 : ℝ)=(20001229818567776409/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3011071835002209/50000000000000000000 : ℝ) ≤ ((44359074983047512591/44360000000000000000 : ℝ)+2*(104239683737/887200000000000 : ℝ)*(17937/100000 : ℝ))^(5791/1024 : ℝ) := by
    rw [show (44359074983047512591/44360000000000000000 : ℝ)+2*(104239683737/887200000000000 : ℝ)*(17937/100000 : ℝ)=(1000021296894831/1000000000000000 : ℝ) by norm_num, show 1+2*(3011071835002209/50000000000000000000 : ℝ)=(25003011071835002209/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44359074983047512591/44360000000000000000 : ℝ)*(X 1 0+X 2 0)+(104239683737/887200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (1813/20000 : ℝ)) (hi := (17937/100000 : ℝ)) (c := (44359074983047512591/44360000000000000000 : ℝ)) (alpha := (104239683737/887200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44359074983047512591/44360000000000000000 : ℝ)*(X 0 1+X 2 1)+(104239683737/887200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (1813/20000 : ℝ)) (hi := (17937/100000 : ℝ)) (c := (44359074983047512591/44360000000000000000 : ℝ)) (alpha := (104239683737/887200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44359074983047512591/44360000000000000000 : ℝ)*(X 0 2+X 1 2)+(104239683737/887200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (1813/20000 : ℝ)) (hi := (17937/100000 : ℝ)) (c := (44359074983047512591/44360000000000000000 : ℝ)) (alpha := (104239683737/887200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2667441017/5000000000 : ℝ)*X 2 0+(2540851947/5000000000 : ℝ)*X 2 1+(-285374101/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s3_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1211446953/10000000000 : ℝ)*X 0 0+(2544218499/5000000000 : ℝ)*X 0 1+(5487450503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s3_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5225561789/10000000000 : ℝ)*X 1 0+(-102112351/1000000000 : ℝ)*X 1 1+(1371862613/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s3_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5225561203/10000000000 : ℝ)*X 2 0+(5487451077/10000000000 : ℝ)*X 2 1+(-204224689/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s3_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4017877211/10000000000 : ℝ)*X 0 0+(1177286361/2500000000 : ℝ)*X 0 1+(169372341/500000000 : ℝ)*X 0 2+(4017877211/10000000000 : ℝ)*X 1 0+(1177286361/2500000000 : ℝ)*X 1 1+(169372341/500000000 : ℝ)*X 1 2+(4017877211/10000000000 : ℝ)*X 2 0+(1177286361/2500000000 : ℝ)*X 2 1+(169372341/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_s3_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (581936257787956041684221709/110900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (316940073/50000000000000 : ℝ)*(base19) + (304597053/50000000000000 : ℝ)*(base23) + (2950467/2500000000000 : ℝ)*(lower1) + (38810351/25000000000000 : ℝ)*(upper3) + (49271847/50000000000000 : ℝ)*(lower4) + (9027783/50000000000000 : ℝ)*(upper5) + (163138782667433/10000000000000 : ℝ)*(major0) + (163138782667433/10000000000000 : ℝ)*(major1) + (163138782667433/10000000000000 : ℝ)*(major2) + (129593691/4000000000000 : ℝ)*(sp0) + (1253087044698381/50000000000000 : ℝ)*(sp1) + (313271681939577/12500000000000 : ℝ)*(sp2) + (2506170240360381/100000000000000 : ℝ)*(sp3) + (11821896703729/1562500000000 : ℝ)*(sp4) + (11821896703729/1562500000000 : ℝ)*(f.failure) + (1253087044698381/50000000000000 : ℝ)*(f.sum) + (16031310255159/4436000000000000000000000000 : ℝ)*base66 + (15588075470574801097/443600000000000000000000000000000 : ℝ)*base68 + (7272732016892401097/443600000000000000000000000000000 : ℝ)*base70 + (24031988473094801097/443600000000000000000000000000000 : ℝ)*base72 + (9117976700223/4436000000000000000000000000 : ℝ)*base74 + (60261269497941998903/443600000000000000000000000000000 : ℝ)*base75 + (5293836366263201097/443600000000000000000000000000000 : ℝ)*base78 + (8107958618774401097/443600000000000000000000000000000 : ℝ)*base80 + (18599489292879/4436000000000000000000000000 : ℝ)*base82 + (2182893/156250000000000000000 : ℝ)*base89 + (2182893/156250000000000000000 : ℝ)*base91 + (2182893/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1752_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1813/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1813/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1121/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1752_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1752_box_0 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-82767877/1000000000 : ℝ)*x 0 + (1084628101/2000000000 : ℝ)*x 1 + (5423140079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82767877/1000000000 : ℝ)^5807 ≤ (1213738580379/25000000000000 : ℝ)^4783 := by
    have hnat : (82767877 : ℕ)^5807*25000000000000^4783 ≤ 1213738580379^4783*1000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82767877 1000000000 1213738580379 25000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084628101/2000000000 : ℝ)^5807 ≤ (47572525102197/100000000000000 : ℝ)^4783 := by
    have hnat : (1084628101 : ℕ)^5807*100000000000000^4783 ≤ 47572525102197^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084628101 2000000000 47572525102197 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423140079/10000000000 : ℝ)^5807 ≤ (23786260282611/50000000000000 : ℝ)^4783 := by
    have hnat : (5423140079 : ℕ)^5807*50000000000000^4783 ≤ 23786260282611^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423140079 10000000000 23786260282611 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82767877/1000000000 : ℝ), (1084628101/2000000000 : ℝ), (5423140079/10000000000 : ℝ)] ![(1213738580379/25000000000000 : ℝ), (47572525102197/100000000000000 : ℝ), (23786260282611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82767877/1000000000 : ℝ)|^5807 ≤ (1213738580379/25000000000000 : ℝ)^4783
        have hw : |(-82767877/1000000000 : ℝ)|=(82767877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084628101/2000000000 : ℝ)|^5807 ≤ (47572525102197/100000000000000 : ℝ)^4783
        have hw : |(1084628101/2000000000 : ℝ)|=(1084628101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423140079/10000000000 : ℝ)|^5807 ≤ (23786260282611/50000000000000 : ℝ)^4783
        have hw : |(5423140079/10000000000 : ℝ)|=(5423140079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_1 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597105899/5000000000 : ℝ)*x 0 + (-288946271/2500000000 : ℝ)*x 1 + (5423140649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597105899/5000000000 : ℝ)^5807 ≤ (1410797985831/3125000000000 : ℝ)^4783 := by
    have hnat : (2597105899 : ℕ)^5807*3125000000000^4783 ≤ 1410797985831^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597105899 5000000000 1410797985831 3125000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288946271/2500000000 : ℝ)^5807 ≤ (1456387560791/20000000000000 : ℝ)^4783 := by
    have hnat : (288946271 : ℕ)^5807*20000000000000^4783 ≤ 1456387560791^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288946271 2500000000 1456387560791 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423140649/10000000000 : ℝ)^5807 ≤ (23786263317911/50000000000000 : ℝ)^4783 := by
    have hnat : (5423140649 : ℕ)^5807*50000000000000^4783 ≤ 23786263317911^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423140649 10000000000 23786263317911 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597105899/5000000000 : ℝ), (-288946271/2500000000 : ℝ), (5423140649/10000000000 : ℝ)] ![(1410797985831/3125000000000 : ℝ), (1456387560791/20000000000000 : ℝ), (23786263317911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597105899/5000000000 : ℝ)|^5807 ≤ (1410797985831/3125000000000 : ℝ)^4783
        have hw : |(2597105899/5000000000 : ℝ)|=(2597105899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-288946271/2500000000 : ℝ)|^5807 ≤ (1456387560791/20000000000000 : ℝ)^4783
        have hw : |(-288946271/2500000000 : ℝ)|=(288946271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423140649/10000000000 : ℝ)|^5807 ≤ (23786263317911/50000000000000 : ℝ)^4783
        have hw : |(5423140649/10000000000 : ℝ)|=(5423140649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_2 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519421247/1000000000 : ℝ)*x 0 + (2711570089/5000000000 : ℝ)*x 1 + (-1155784813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519421247/1000000000 : ℝ)^5807 ≤ (45145542637729/100000000000000 : ℝ)^4783 := by
    have hnat : (519421247 : ℕ)^5807*100000000000000^4783 ≤ 45145542637729^4783*1000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519421247 1000000000 45145542637729 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711570089/5000000000 : ℝ)^5807 ≤ (47572521619589/100000000000000 : ℝ)^4783 := by
    have hnat : (2711570089 : ℕ)^5807*100000000000000^4783 ≤ 47572521619589^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711570089 5000000000 47572521619589 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1155784813/10000000000 : ℝ)^5807 ≤ (1820483932749/25000000000000 : ℝ)^4783 := by
    have hnat : (1155784813 : ℕ)^5807*25000000000000^4783 ≤ 1820483932749^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155784813 10000000000 1820483932749 25000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519421247/1000000000 : ℝ), (2711570089/5000000000 : ℝ), (-1155784813/10000000000 : ℝ)] ![(45145542637729/100000000000000 : ℝ), (47572521619589/100000000000000 : ℝ), (1820483932749/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519421247/1000000000 : ℝ)|^5807 ≤ (45145542637729/100000000000000 : ℝ)^4783
        have hw : |(519421247/1000000000 : ℝ)|=(519421247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711570089/5000000000 : ℝ)|^5807 ≤ (47572521619589/100000000000000 : ℝ)^4783
        have hw : |(2711570089/5000000000 : ℝ)|=(2711570089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1155784813/10000000000 : ℝ)|^5807 ≤ (1820483932749/25000000000000 : ℝ)^4783
        have hw : |(-1155784813/10000000000 : ℝ)|=(1155784813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_3 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1135688947/2500000000 : ℝ)*x 0 + (1896280039/5000000000 : ℝ)*x 1 + (758512077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1135688947/2500000000 : ℝ)^5807 ≤ (4795836538911/12500000000000 : ℝ)^4783 := by
    have hnat : (1135688947 : ℕ)^5807*12500000000000^4783 ≤ 4795836538911^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135688947 2500000000 4795836538911 12500000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1896280039/5000000000 : ℝ)^5807 ≤ (30816652321233/100000000000000 : ℝ)^4783 := by
    have hnat : (1896280039 : ℕ)^5807*100000000000000^4783 ≤ 30816652321233^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896280039 5000000000 30816652321233 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (758512077/2000000000 : ℝ)^5807 ≤ (385208191873/1250000000000 : ℝ)^4783 := by
    have hnat : (758512077 : ℕ)^5807*1250000000000^4783 ≤ 385208191873^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758512077 2000000000 385208191873 1250000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1135688947/2500000000 : ℝ), (1896280039/5000000000 : ℝ), (758512077/2000000000 : ℝ)] ![(4795836538911/12500000000000 : ℝ), (30816652321233/100000000000000 : ℝ), (385208191873/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1135688947/2500000000 : ℝ)|^5807 ≤ (4795836538911/12500000000000 : ℝ)^4783
        have hw : |(1135688947/2500000000 : ℝ)|=(1135688947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1896280039/5000000000 : ℝ)|^5807 ≤ (30816652321233/100000000000000 : ℝ)^4783
        have hw : |(1896280039/5000000000 : ℝ)|=(1896280039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(758512077/2000000000 : ℝ)|^5807 ≤ (385208191873/1250000000000 : ℝ)^4783
        have hw : |(758512077/2000000000 : ℝ)|=(758512077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_4 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-163412767/1000000000 : ℝ)*x 0 + (5128773443/10000000000 : ℝ)*x 1 + (5128774267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163412767/1000000000 : ℝ)^5807 ≤ (11088100190417/100000000000000 : ℝ)^4783 := by
    have hnat : (163412767 : ℕ)^5807*100000000000000^4783 ≤ 11088100190417^4783*1000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163412767 1000000000 11088100190417 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128773443/10000000000 : ℝ)^5807 ≤ (22227972782589/50000000000000 : ℝ)^4783 := by
    have hnat : (5128773443 : ℕ)^5807*50000000000000^4783 ≤ 22227972782589^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128773443 10000000000 22227972782589 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128774267/10000000000 : ℝ)^5807 ≤ (44455954236693/100000000000000 : ℝ)^4783 := by
    have hnat : (5128774267 : ℕ)^5807*100000000000000^4783 ≤ 44455954236693^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128774267 10000000000 44455954236693 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-163412767/1000000000 : ℝ), (5128773443/10000000000 : ℝ), (5128774267/10000000000 : ℝ)] ![(11088100190417/100000000000000 : ℝ), (22227972782589/50000000000000 : ℝ), (44455954236693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-163412767/1000000000 : ℝ)|^5807 ≤ (11088100190417/100000000000000 : ℝ)^4783
        have hw : |(-163412767/1000000000 : ℝ)|=(163412767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128773443/10000000000 : ℝ)|^5807 ≤ (22227972782589/50000000000000 : ℝ)^4783
        have hw : |(5128773443/10000000000 : ℝ)|=(5128773443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128774267/10000000000 : ℝ)|^5807 ≤ (44455954236693/100000000000000 : ℝ)^4783
        have hw : |(5128774267/10000000000 : ℝ)|=(5128774267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_5 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695550173/5000000000 : ℝ)*x 0 + (-2013943/15625000 : ℝ)*x 1 + (5128773099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695550173/5000000000 : ℝ)^5807 ≤ (23615753952579/50000000000000 : ℝ)^4783 := by
    have hnat : (2695550173 : ℕ)^5807*50000000000000^4783 ≤ 23615753952579^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695550173 5000000000 23615753952579 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013943/15625000 : ℝ)^5807 ≤ (8312550144333/100000000000000 : ℝ)^4783 := by
    have hnat : (2013943 : ℕ)^5807*100000000000000^4783 ≤ 8312550144333^4783*15625000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013943 15625000 8312550144333 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128773099/10000000000 : ℝ)^5807 ≤ (44455941945031/100000000000000 : ℝ)^4783 := by
    have hnat : (5128773099 : ℕ)^5807*100000000000000^4783 ≤ 44455941945031^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128773099 10000000000 44455941945031 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695550173/5000000000 : ℝ), (-2013943/15625000 : ℝ), (5128773099/10000000000 : ℝ)] ![(23615753952579/50000000000000 : ℝ), (8312550144333/100000000000000 : ℝ), (44455941945031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695550173/5000000000 : ℝ)|^5807 ≤ (23615753952579/50000000000000 : ℝ)^4783
        have hw : |(2695550173/5000000000 : ℝ)|=(2695550173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2013943/15625000 : ℝ)|^5807 ≤ (8312550144333/100000000000000 : ℝ)^4783
        have hw : |(-2013943/15625000 : ℝ)|=(2013943/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128773099/10000000000 : ℝ)|^5807 ≤ (44455941945031/100000000000000 : ℝ)^4783
        have hw : |(5128773099/10000000000 : ℝ)|=(5128773099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_6 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391099601/10000000000 : ℝ)*x 0 + (641096739/1250000000 : ℝ)*x 1 + (-644461719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391099601/10000000000 : ℝ)^5807 ≤ (11807874995209/25000000000000 : ℝ)^4783 := by
    have hnat : (5391099601 : ℕ)^5807*25000000000000^4783 ≤ 11807874995209^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391099601 10000000000 11807874995209 25000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641096739/1250000000 : ℝ)^5807 ≤ (8891190100157/20000000000000 : ℝ)^4783 := by
    have hnat : (641096739 : ℕ)^5807*20000000000000^4783 ≤ 8891190100157^4783*1250000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641096739 1250000000 8891190100157 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644461719/5000000000 : ℝ)^5807 ≤ (8312549502277/100000000000000 : ℝ)^4783 := by
    have hnat : (644461719 : ℕ)^5807*100000000000000^4783 ≤ 8312549502277^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644461719 5000000000 8312549502277 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391099601/10000000000 : ℝ), (641096739/1250000000 : ℝ), (-644461719/5000000000 : ℝ)] ![(11807874995209/25000000000000 : ℝ), (8891190100157/20000000000000 : ℝ), (8312549502277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391099601/10000000000 : ℝ)|^5807 ≤ (11807874995209/25000000000000 : ℝ)^4783
        have hw : |(5391099601/10000000000 : ℝ)|=(5391099601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641096739/1250000000 : ℝ)|^5807 ≤ (8891190100157/20000000000000 : ℝ)^4783
        have hw : |(641096739/1250000000 : ℝ)|=(641096739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-644461719/5000000000 : ℝ)|^5807 ≤ (8312549502277/100000000000000 : ℝ)^4783
        have hw : |(-644461719/5000000000 : ℝ)|=(644461719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_7 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1726865161/5000000000 : ℝ)*x 0 + (4334965417/10000000000 : ℝ)*x 1 + (2167482971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1726865161/5000000000 : ℝ)^5807 ≤ (27506787044907/100000000000000 : ℝ)^4783 := by
    have hnat : (1726865161 : ℕ)^5807*100000000000000^4783 ≤ 27506787044907^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726865161 5000000000 27506787044907 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4334965417/10000000000 : ℝ)^5807 ≤ (36246603801459/100000000000000 : ℝ)^4783 := by
    have hnat : (4334965417 : ℕ)^5807*100000000000000^4783 ≤ 36246603801459^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334965417 10000000000 36246603801459 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2167482971/5000000000 : ℝ)^5807 ≤ (4530826141379/12500000000000 : ℝ)^4783 := by
    have hnat : (2167482971 : ℕ)^5807*12500000000000^4783 ≤ 4530826141379^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167482971 5000000000 4530826141379 12500000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1726865161/5000000000 : ℝ), (4334965417/10000000000 : ℝ), (2167482971/5000000000 : ℝ)] ![(27506787044907/100000000000000 : ℝ), (36246603801459/100000000000000 : ℝ), (4530826141379/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1726865161/5000000000 : ℝ)|^5807 ≤ (27506787044907/100000000000000 : ℝ)^4783
        have hw : |(1726865161/5000000000 : ℝ)|=(1726865161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4334965417/10000000000 : ℝ)|^5807 ≤ (36246603801459/100000000000000 : ℝ)^4783
        have hw : |(4334965417/10000000000 : ℝ)|=(4334965417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2167482971/5000000000 : ℝ)|^5807 ≤ (4530826141379/12500000000000 : ℝ)^4783
        have hw : |(2167482971/5000000000 : ℝ)|=(2167482971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_8 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1458690381/10000000000 : ℝ)*x 0 + (1226107311/2500000000 : ℝ)*x 1 + (68564503/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1458690381/10000000000 : ℝ)^5807 ≤ (9659945297321/100000000000000 : ℝ)^4783 := by
    have hnat : (1458690381 : ℕ)^5807*100000000000000^4783 ≤ 9659945297321^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458690381 10000000000 9659945297321 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1226107311/2500000000 : ℝ)^5807 ≤ (42106202281421/100000000000000 : ℝ)^4783 := by
    have hnat : (1226107311 : ℕ)^5807*100000000000000^4783 ≤ 42106202281421^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226107311 2500000000 42106202281421 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68564503/125000000 : ℝ)^5807 ≤ (24116926200059/50000000000000 : ℝ)^4783 := by
    have hnat : (68564503 : ℕ)^5807*50000000000000^4783 ≤ 24116926200059^4783*125000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68564503 125000000 24116926200059 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1458690381/10000000000 : ℝ), (1226107311/2500000000 : ℝ), (68564503/125000000 : ℝ)] ![(9659945297321/100000000000000 : ℝ), (42106202281421/100000000000000 : ℝ), (24116926200059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1458690381/10000000000 : ℝ)|^5807 ≤ (9659945297321/100000000000000 : ℝ)^4783
        have hw : |(-1458690381/10000000000 : ℝ)|=(1458690381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1226107311/2500000000 : ℝ)|^5807 ≤ (42106202281421/100000000000000 : ℝ)^4783
        have hw : |(1226107311/2500000000 : ℝ)|=(1226107311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68564503/125000000 : ℝ)|^5807 ≤ (24116926200059/50000000000000 : ℝ)^4783
        have hw : |(68564503/125000000 : ℝ)|=(68564503/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_9 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576399451/5000000000 : ℝ)*x 0 + (-1126329137/10000000000 : ℝ)*x 1 + (2742580101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576399451/5000000000 : ℝ)^5807 ≤ (44708908523443/100000000000000 : ℝ)^4783 := by
    have hnat : (2576399451 : ℕ)^5807*100000000000000^4783 ≤ 44708908523443^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576399451 5000000000 44708908523443 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126329137/10000000000 : ℝ)^5807 ≤ (7057239466509/100000000000000 : ℝ)^4783 := by
    have hnat : (1126329137 : ℕ)^5807*100000000000000^4783 ≤ 7057239466509^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126329137 10000000000 7057239466509 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2742580101/5000000000 : ℝ)^5807 ≤ (1929354079777/4000000000000 : ℝ)^4783 := by
    have hnat : (2742580101 : ℕ)^5807*4000000000000^4783 ≤ 1929354079777^4783*5000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742580101 5000000000 1929354079777 4000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576399451/5000000000 : ℝ), (-1126329137/10000000000 : ℝ), (2742580101/5000000000 : ℝ)] ![(44708908523443/100000000000000 : ℝ), (7057239466509/100000000000000 : ℝ), (1929354079777/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576399451/5000000000 : ℝ)|^5807 ≤ (44708908523443/100000000000000 : ℝ)^4783
        have hw : |(2576399451/5000000000 : ℝ)|=(2576399451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126329137/10000000000 : ℝ)|^5807 ≤ (7057239466509/100000000000000 : ℝ)^4783
        have hw : |(-1126329137/10000000000 : ℝ)|=(1126329137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2742580101/5000000000 : ℝ)|^5807 ≤ (1929354079777/4000000000000 : ℝ)^4783
        have hw : |(2742580101/5000000000 : ℝ)|=(2742580101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_10 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152799051/10000000000 : ℝ)*x 0 + (5485160013/10000000000 : ℝ)*x 1 + (-1126329197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152799051/10000000000 : ℝ)^5807 ≤ (22354455046521/50000000000000 : ℝ)^4783 := by
    have hnat : (5152799051 : ℕ)^5807*50000000000000^4783 ≤ 22354455046521^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152799051 10000000000 22354455046521 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485160013/10000000000 : ℝ)^5807 ≤ (12058462494159/25000000000000 : ℝ)^4783 := by
    have hnat : (5485160013 : ℕ)^5807*25000000000000^4783 ≤ 12058462494159^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485160013 10000000000 12058462494159 25000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126329197/10000000000 : ℝ)^5807 ≤ (7057239922937/100000000000000 : ℝ)^4783 := by
    have hnat : (1126329197 : ℕ)^5807*100000000000000^4783 ≤ 7057239922937^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126329197 10000000000 7057239922937 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152799051/10000000000 : ℝ), (5485160013/10000000000 : ℝ), (-1126329197/10000000000 : ℝ)] ![(22354455046521/50000000000000 : ℝ), (12058462494159/25000000000000 : ℝ), (7057239922937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152799051/10000000000 : ℝ)|^5807 ≤ (22354455046521/50000000000000 : ℝ)^4783
        have hw : |(5152799051/10000000000 : ℝ)|=(5152799051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485160013/10000000000 : ℝ)|^5807 ≤ (12058462494159/25000000000000 : ℝ)^4783
        have hw : |(5485160013/10000000000 : ℝ)|=(5485160013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126329197/10000000000 : ℝ)|^5807 ≤ (7057239922937/100000000000000 : ℝ)^4783
        have hw : |(-1126329197/10000000000 : ℝ)|=(1126329197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_11 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4761634851/10000000000 : ℝ)*x 0 + (919463731/2500000000 : ℝ)*x 1 + (735571089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4761634851/10000000000 : ℝ)^5807 ≤ (40622475161493/100000000000000 : ℝ)^4783 := by
    have hnat : (4761634851 : ℕ)^5807*100000000000000^4783 ≤ 40622475161493^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4761634851 10000000000 40622475161493 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (919463731/2500000000 : ℝ)^5807 ≤ (29688759859991/100000000000000 : ℝ)^4783 := by
    have hnat : (919463731 : ℕ)^5807*100000000000000^4783 ≤ 29688759859991^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919463731 2500000000 29688759859991 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735571089/2000000000 : ℝ)^5807 ≤ (1484438248303/5000000000000 : ℝ)^4783 := by
    have hnat : (735571089 : ℕ)^5807*5000000000000^4783 ≤ 1484438248303^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735571089 2000000000 1484438248303 5000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4761634851/10000000000 : ℝ), (919463731/2500000000 : ℝ), (735571089/2000000000 : ℝ)] ![(40622475161493/100000000000000 : ℝ), (29688759859991/100000000000000 : ℝ), (1484438248303/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4761634851/10000000000 : ℝ)|^5807 ≤ (40622475161493/100000000000000 : ℝ)^4783
        have hw : |(4761634851/10000000000 : ℝ)|=(4761634851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(919463731/2500000000 : ℝ)|^5807 ≤ (29688759859991/100000000000000 : ℝ)^4783
        have hw : |(919463731/2500000000 : ℝ)|=(919463731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(735571089/2000000000 : ℝ)|^5807 ≤ (1484438248303/5000000000000 : ℝ)^4783
        have hw : |(735571089/2000000000 : ℝ)|=(735571089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_12 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-989285229/10000000000 : ℝ)*x 0 + (1408594641/2500000000 : ℝ)*x 1 + (1019740767/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989285229/10000000000 : ℝ)^5807 ≤ (3014382310679/50000000000000 : ℝ)^4783 := by
    have hnat : (989285229 : ℕ)^5807*50000000000000^4783 ≤ 3014382310679^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989285229 10000000000 3014382310679 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1408594641/2500000000 : ℝ)^5807 ≤ (49831533928373/100000000000000 : ℝ)^4783 := by
    have hnat : (1408594641 : ℕ)^5807*100000000000000^4783 ≤ 49831533928373^4783*2500000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408594641 2500000000 49831533928373 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019740767/2000000000 : ℝ)^5807 ≤ (8827940286137/20000000000000 : ℝ)^4783 := by
    have hnat : (1019740767 : ℕ)^5807*20000000000000^4783 ≤ 8827940286137^4783*2000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019740767 2000000000 8827940286137 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989285229/10000000000 : ℝ), (1408594641/2500000000 : ℝ), (1019740767/2000000000 : ℝ)] ![(3014382310679/50000000000000 : ℝ), (49831533928373/100000000000000 : ℝ), (8827940286137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989285229/10000000000 : ℝ)|^5807 ≤ (3014382310679/50000000000000 : ℝ)^4783
        have hw : |(-989285229/10000000000 : ℝ)|=(989285229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1408594641/2500000000 : ℝ)|^5807 ≤ (49831533928373/100000000000000 : ℝ)^4783
        have hw : |(1408594641/2500000000 : ℝ)|=(1408594641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019740767/2000000000 : ℝ)|^5807 ≤ (8827940286137/20000000000000 : ℝ)^4783
        have hw : |(1019740767/2000000000 : ℝ)|=(1019740767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_13 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5411285557/10000000000 : ℝ)*x 0 + (-162733357/1250000000 : ℝ)*x 1 + (5098703531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411285557/10000000000 : ℝ)^5807 ≤ (47446297378553/100000000000000 : ℝ)^4783 := by
    have hnat : (5411285557 : ℕ)^5807*100000000000000^4783 ≤ 47446297378553^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411285557 10000000000 47446297378553 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162733357/1250000000 : ℝ)^5807 ≤ (1682800875523/20000000000000 : ℝ)^4783 := by
    have hnat : (162733357 : ℕ)^5807*20000000000000^4783 ≤ 1682800875523^4783*1250000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162733357 1250000000 1682800875523 20000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5098703531/10000000000 : ℝ)^5807 ≤ (4413969823551/10000000000000 : ℝ)^4783 := by
    have hnat : (5098703531 : ℕ)^5807*10000000000000^4783 ≤ 4413969823551^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098703531 10000000000 4413969823551 10000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411285557/10000000000 : ℝ), (-162733357/1250000000 : ℝ), (5098703531/10000000000 : ℝ)] ![(47446297378553/100000000000000 : ℝ), (1682800875523/20000000000000 : ℝ), (4413969823551/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411285557/10000000000 : ℝ)|^5807 ≤ (47446297378553/100000000000000 : ℝ)^4783
        have hw : |(5411285557/10000000000 : ℝ)|=(5411285557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-162733357/1250000000 : ℝ)|^5807 ≤ (1682800875523/20000000000000 : ℝ)^4783
        have hw : |(-162733357/1250000000 : ℝ)|=(162733357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5098703531/10000000000 : ℝ)|^5807 ≤ (4413969823551/10000000000000 : ℝ)^4783
        have hw : |(5098703531/10000000000 : ℝ)|=(5098703531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_14 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (676410671/1250000000 : ℝ)*x 0 + (5098703963/10000000000 : ℝ)*x 1 + (-1301866533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676410671/1250000000 : ℝ)^5807 ≤ (47446295366613/100000000000000 : ℝ)^4783 := by
    have hnat : (676410671 : ℕ)^5807*100000000000000^4783 ≤ 47446295366613^4783*1250000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676410671 1250000000 47446295366613 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5098703963/10000000000 : ℝ)^5807 ≤ (22069851388011/50000000000000 : ℝ)^4783 := by
    have hnat : (5098703963 : ℕ)^5807*50000000000000^4783 ≤ 22069851388011^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098703963 10000000000 22069851388011 50000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301866533/10000000000 : ℝ)^5807 ≤ (8414001843127/100000000000000 : ℝ)^4783 := by
    have hnat : (1301866533 : ℕ)^5807*100000000000000^4783 ≤ 8414001843127^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301866533 10000000000 8414001843127 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676410671/1250000000 : ℝ), (5098703963/10000000000 : ℝ), (-1301866533/10000000000 : ℝ)] ![(47446295366613/100000000000000 : ℝ), (22069851388011/50000000000000 : ℝ), (8414001843127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676410671/1250000000 : ℝ)|^5807 ≤ (47446295366613/100000000000000 : ℝ)^4783
        have hw : |(676410671/1250000000 : ℝ)|=(676410671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5098703963/10000000000 : ℝ)|^5807 ≤ (22069851388011/50000000000000 : ℝ)^4783
        have hw : |(5098703963/10000000000 : ℝ)|=(5098703963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1301866533/10000000000 : ℝ)|^5807 ≤ (8414001843127/100000000000000 : ℝ)^4783
        have hw : |(-1301866533/10000000000 : ℝ)|=(1301866533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1752_box_15 (p : ℝ) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3337279259/10000000000 : ℝ)*x 0 + (548768581/1250000000 : ℝ)*x 1 + (4390149733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3337279259/10000000000 : ℝ)^5807 ≤ (527697340683/2000000000000 : ℝ)^4783 := by
    have hnat : (3337279259 : ℕ)^5807*2000000000000^4783 ≤ 527697340683^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3337279259 10000000000 527697340683 2000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548768581/1250000000 : ℝ)^5807 ≤ (36807560956309/100000000000000 : ℝ)^4783 := by
    have hnat : (548768581 : ℕ)^5807*100000000000000^4783 ≤ 36807560956309^4783*1250000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548768581 1250000000 36807560956309 100000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4390149733/10000000000 : ℝ)^5807 ≤ (3680757200063/10000000000000 : ℝ)^4783 := by
    have hnat : (4390149733 : ℕ)^5807*10000000000000^4783 ≤ 3680757200063^4783*10000000000^5807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4390149733 10000000000 3680757200063 10000000000000 5807 4783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5807/1024 : ℝ)) 5807 4783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3337279259/10000000000 : ℝ), (548768581/1250000000 : ℝ), (4390149733/10000000000 : ℝ)] ![(527697340683/2000000000000 : ℝ), (36807560956309/100000000000000 : ℝ), (3680757200063/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3337279259/10000000000 : ℝ)|^5807 ≤ (527697340683/2000000000000 : ℝ)^4783
        have hw : |(3337279259/10000000000 : ℝ)|=(3337279259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548768581/1250000000 : ℝ)|^5807 ≤ (36807560956309/100000000000000 : ℝ)^4783
        have hw : |(548768581/1250000000 : ℝ)|=(548768581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4390149733/10000000000 : ℝ)|^5807 ≤ (3680757200063/10000000000000 : ℝ)^4783
        have hw : |(4390149733/10000000000 : ℝ)|=(4390149733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1752_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1121/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1813/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(68951/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58211/100000 : ℝ) ∧ (40841/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (11617/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1121/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1813/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1121/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1813/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1121/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1813/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1121/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1813/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1121/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1813/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1121/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1813/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1813/20000 : ℝ) ^ (5791/1024 : ℝ) ≤ (126949168877627/100000000000000000000 : ℝ) := by
    have hpowers : (1813/20000 : ℝ)^5791 ≤ (126949168877627/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1813 : ℕ)^5791*100000000000000000000^1024 ≤ 126949168877627^1024*20000^5791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1813 20000 126949168877627 100000000000000000000 5791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1813/20000 : ℝ)) (X := (126949168877627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1121/6250 : ℝ) ^ (5791/1024 : ℝ) ≤ (3010122611331451/50000000000000000000 : ℝ) := by
    have hpowers : (1121/6250 : ℝ)^5791 ≤ (3010122611331451/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1121 : ℕ)^5791*50000000000000000000^1024 ≤ 3010122611331451^1024*6250^5791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1121 6250 3010122611331451 50000000000000000000 5791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1121/6250 : ℝ)) (X := (3010122611331451/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000126949168877627/50000000000000000000 : ℝ) ≤ (2500001122395209/2500000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (50000126949168877627/50000000000000000000 : ℝ)^1024 ≤ (2500001122395209/2500000000000000 : ℝ)^5791 := by
      have hnat : (50000126949168877627 : ℕ)^1024*2500000000000000^5791 ≤ 2500001122395209^5791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000126949168877627 50000000000000000000 2500001122395209 2500000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500001122395209/2500000000000000 : ℝ)) (X := (50000126949168877627/50000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100006147194391540529/100000000000000000000 : ℝ) ≤ (5000054347848383/5000000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (100006147194391540529/100000000000000000000 : ℝ)^1024 ≤ (5000054347848383/5000000000000000 : ℝ)^5791 := by
      have hnat : (100006147194391540529 : ℕ)^1024*5000000000000000^5791 ≤ 5000054347848383^5791*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100006147194391540529 100000000000000000000 5000054347848383 5000000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000054347848383/5000000000000000 : ℝ)) (X := (100006147194391540529/100000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25003010122611331451/25000000000000000000 : ℝ) ≤ (1250026612726587/1250000000000000 : ℝ) ^ (5791/1024 : ℝ) := by
    have hpowers : (25003010122611331451/25000000000000000000 : ℝ)^1024 ≤ (1250026612726587/1250000000000000 : ℝ)^5791 := by
      have hnat : (25003010122611331451 : ℕ)^1024*1250000000000000^5791 ≤ 1250026612726587^5791*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003010122611331451 25000000000000000000 1250026612726587 1250000000000000 1024 5791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250026612726587/1250000000000000 : ℝ)) (X := (25003010122611331451/25000000000000000000 : ℝ)) (by norm_num) 5791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(126949168877627/100000000000000000000 : ℝ) ≤ ((11088518821273723157/11088750000000000000 : ℝ)+2*(10420611593/88710000000000 : ℝ)*(1813/20000 : ℝ))^(5791/1024 : ℝ) := by
    rw [show (11088518821273723157/11088750000000000000 : ℝ)+2*(10420611593/88710000000000 : ℝ)*(1813/20000 : ℝ)=(2500001122395209/2500000000000000 : ℝ) by norm_num, show 1+2*(126949168877627/100000000000000000000 : ℝ)=(50000126949168877627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3010122611331451/50000000000000000000 : ℝ)+(126949168877627/100000000000000000000 : ℝ) ≤ ((11088518821273723157/11088750000000000000 : ℝ)+(10420611593/88710000000000 : ℝ)*((1121/6250 : ℝ)+(1813/20000 : ℝ)))^(5791/1024 : ℝ) := by
    rw [show (11088518821273723157/11088750000000000000 : ℝ)+(10420611593/88710000000000 : ℝ)*((1121/6250 : ℝ)+(1813/20000 : ℝ))=(5000054347848383/5000000000000000 : ℝ) by norm_num, show 1+(3010122611331451/50000000000000000000 : ℝ)+(126949168877627/100000000000000000000 : ℝ)=(100006147194391540529/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3010122611331451/50000000000000000000 : ℝ) ≤ ((11088518821273723157/11088750000000000000 : ℝ)+2*(10420611593/88710000000000 : ℝ)*(1121/6250 : ℝ))^(5791/1024 : ℝ) := by
    rw [show (11088518821273723157/11088750000000000000 : ℝ)+2*(10420611593/88710000000000 : ℝ)*(1121/6250 : ℝ)=(1250026612726587/1250000000000000 : ℝ) by norm_num, show 1+2*(3010122611331451/50000000000000000000 : ℝ)=(25003010122611331451/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11088518821273723157/11088750000000000000 : ℝ)*(X 1 0+X 2 0)+(10420611593/88710000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (1813/20000 : ℝ)) (hi := (1121/6250 : ℝ)) (c := (11088518821273723157/11088750000000000000 : ℝ)) (alpha := (10420611593/88710000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11088518821273723157/11088750000000000000 : ℝ)*(X 0 1+X 2 1)+(10420611593/88710000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (1813/20000 : ℝ)) (hi := (1121/6250 : ℝ)) (c := (11088518821273723157/11088750000000000000 : ℝ)) (alpha := (10420611593/88710000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11088518821273723157/11088750000000000000 : ℝ)*(X 0 2+X 1 2)+(10420611593/88710000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5791/1024 : ℝ)) (lo := (1813/20000 : ℝ)) (hi := (1121/6250 : ℝ)) (c := (11088518821273723157/11088750000000000000 : ℝ)) (alpha := (10420611593/88710000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-82767877/1000000000 : ℝ)*X 0 0+(1084628101/2000000000 : ℝ)*X 0 1+(5423140079/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2597105899/5000000000 : ℝ)*X 1 0+(-288946271/2500000000 : ℝ)*X 1 1+(5423140649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((519421247/1000000000 : ℝ)*X 2 0+(2711570089/5000000000 : ℝ)*X 2 1+(-1155784813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1135688947/2500000000 : ℝ)*X 0 0+(1896280039/5000000000 : ℝ)*X 0 1+(758512077/2000000000 : ℝ)*X 0 2+(1135688947/2500000000 : ℝ)*X 1 0+(1896280039/5000000000 : ℝ)*X 1 1+(758512077/2000000000 : ℝ)*X 1 2+(1135688947/2500000000 : ℝ)*X 2 0+(1896280039/5000000000 : ℝ)*X 2 1+(758512077/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-163412767/1000000000 : ℝ)*X 0 0+(5128773443/10000000000 : ℝ)*X 0 1+(5128774267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2695550173/5000000000 : ℝ)*X 1 0+(-2013943/15625000 : ℝ)*X 1 1+(5128773099/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5391099601/10000000000 : ℝ)*X 2 0+(641096739/1250000000 : ℝ)*X 2 1+(-644461719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1726865161/5000000000 : ℝ)*X 0 0+(4334965417/10000000000 : ℝ)*X 0 1+(2167482971/5000000000 : ℝ)*X 0 2+(1726865161/5000000000 : ℝ)*X 1 0+(4334965417/10000000000 : ℝ)*X 1 1+(2167482971/5000000000 : ℝ)*X 1 2+(1726865161/5000000000 : ℝ)*X 2 0+(4334965417/10000000000 : ℝ)*X 2 1+(2167482971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1458690381/10000000000 : ℝ)*X 0 0+(1226107311/2500000000 : ℝ)*X 0 1+(68564503/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576399451/5000000000 : ℝ)*X 1 0+(-1126329137/10000000000 : ℝ)*X 1 1+(2742580101/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152799051/10000000000 : ℝ)*X 2 0+(5485160013/10000000000 : ℝ)*X 2 1+(-1126329197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4761634851/10000000000 : ℝ)*X 0 0+(919463731/2500000000 : ℝ)*X 0 1+(735571089/2000000000 : ℝ)*X 0 2+(4761634851/10000000000 : ℝ)*X 1 0+(919463731/2500000000 : ℝ)*X 1 1+(735571089/2000000000 : ℝ)*X 1 2+(4761634851/10000000000 : ℝ)*X 2 0+(919463731/2500000000 : ℝ)*X 2 1+(735571089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-989285229/10000000000 : ℝ)*X 0 0+(1408594641/2500000000 : ℝ)*X 0 1+(1019740767/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5411285557/10000000000 : ℝ)*X 1 0+(-162733357/1250000000 : ℝ)*X 1 1+(5098703531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((676410671/1250000000 : ℝ)*X 2 0+(5098703963/10000000000 : ℝ)*X 2 1+(-1301866533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3337279259/10000000000 : ℝ)*X 0 0+(548768581/1250000000 : ℝ)*X 0 1+(4390149733/10000000000 : ℝ)*X 0 2+(3337279259/10000000000 : ℝ)*X 1 0+(548768581/1250000000 : ℝ)*X 1 1+(4390149733/10000000000 : ℝ)*X 1 2+(3337279259/10000000000 : ℝ)*X 2 0+(548768581/1250000000 : ℝ)*X 2 1+(4390149733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1752_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-68951/100000 : ℝ) ≤ (-2038798379064491393506920877/2957000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9950833/50000000000000 : ℝ)*(upper1) + (13031649/20000000000000 : ℝ)*(lower4) + (5065437/25000000000000 : ℝ)*(upper5) + (1056506885205463/100000000000000 : ℝ)*(major0) + (1056506885205463/100000000000000 : ℝ)*(major1) + (1056506885205463/100000000000000 : ℝ)*(major2) + (2790807063/50000000000000 : ℝ)*(sp1) + (2662740463/100000000000000 : ℝ)*(sp2) + (11703997/1250000000000 : ℝ)*(sp3) + (1646009433802821/100000000000000 : ℝ)*(sp4) + (82300326427617/5000000000000 : ℝ)*(sp5) + (1646009447426003/100000000000000 : ℝ)*(sp6) + (489983458442387/100000000000000 : ℝ)*(sp7) + (535272729/20000000000000 : ℝ)*(sp12) + (489984394762147/100000000000000 : ℝ)*(f.failure) + (823006055083233/50000000000000 : ℝ)*(f.sum) + (23959446974869/8871000000000000000000000000 : ℝ)*base65 + (781114875178543897/369625000000000000000000000000000 : ℝ)*base67 + (780483032303706103/369625000000000000000000000000000 : ℝ)*base70 + (24035074456043897/369625000000000000000000000000000 : ℝ)*base71 + (34431968027593/8871000000000000000000000000 : ℝ)*base73 + (1385124349674206103/369625000000000000000000000000000 : ℝ)*base76 + (640299665040418897/369625000000000000000000000000000 : ℝ)*base77 + (149699811236331103/369625000000000000000000000000000 : ℝ)*base80 + (10371959093573/8871000000000000000000000000 : ℝ)*base82 + (71830001/10000000000000000000000 : ℝ)*base90 + (71830001/10000000000000000000000 : ℝ)*base92 + (71830001/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58211/100000 : ℝ) ≤ (53792668281168816756049678200627/92406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60937633/100000000000000 : ℝ)*(upper0) + (1171781/12500000000000 : ℝ)*(lower1) + (113476603/100000000000000 : ℝ)*(upper4) + (1181227371107539/100000000000000 : ℝ)*(major0) + (1181227371107539/100000000000000 : ℝ)*(major1) + (1181227371107539/100000000000000 : ℝ)*(major2) + (1795221970368257/100000000000000 : ℝ)*(sp0) + (897610240341613/50000000000000 : ℝ)*(sp1) + (359044168888979/20000000000000 : ℝ)*(sp2) + (547825998232339/100000000000000 : ℝ)*(sp3) + (2867453921/100000000000000 : ℝ)*(sp5) + (625923063/25000000000000 : ℝ)*(sp6) + (491942647/50000000000000 : ℝ)*(sp7) + (137776889/10000000000000 : ℝ)*(sp8) + (273913491058817/50000000000000 : ℝ)*(f.failure) + (1795223348137147/100000000000000 : ℝ)*(f.sum) + (31738208997017/4435500000000000000000000000 : ℝ)*base65 + (563714136457693541/369625000000000000000000000000000 : ℝ)*base67 + (629045180369431459/369625000000000000000000000000000 : ℝ)*base70 + (2642203915038568541/369625000000000000000000000000000 : ℝ)*base71 + (28730694642899/4435500000000000000000000000 : ℝ)*base73 + (1368068652736818541/369625000000000000000000000000000 : ℝ)*base75 + (650377923136568541/369625000000000000000000000000000 : ℝ)*base77 + (2772869546098568541/369625000000000000000000000000000 : ℝ)*base79 + (20605531437281/4435500000000000000000000000 : ℝ)*base81 + (48948389/5000000000000000000000 : ℝ)*base89 + (48948389/5000000000000000000000 : ℝ)*base91 + (48948389/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (40841/50000 : ℝ) ≤ (150962771872372126363398897714349/184812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2700961/12500000000000 : ℝ)*(upper0) + (6595671/50000000000000 : ℝ)*(lower3) + (887419/100000000000000 : ℝ)*(upper4) + (1138635320223919/100000000000000 : ℝ)*(major0) + (1138635320223919/100000000000000 : ℝ)*(major1) + (1138635320223919/100000000000000 : ℝ)*(major2) + (2990604177/50000000000000 : ℝ)*(sp1) + (715623503/100000000000000 : ℝ)*(sp3) + (98632549/50000000000000 : ℝ)*(sp4) + (860984002759553/50000000000000 : ℝ)*(sp8) + (1721962827519363/100000000000000 : ℝ)*(sp9) + (1721968808727717/100000000000000 : ℝ)*(sp10) + (66009127577179/12500000000000 : ℝ)*(sp11) + (302971757/50000000000000 : ℝ)*(sp12) + (105614747248187/20000000000000 : ℝ)*(f.failure) + (1721968808727717/100000000000000 : ℝ)*(f.sum) + (2233914590941/887100000000000000000000000 : ℝ)*base65 + (3885136910761844239/369625000000000000000000000000000 : ℝ)*base68 + (2412658144518719239/369625000000000000000000000000000 : ℝ)*base70 + (133516101820094239/369625000000000000000000000000000 : ℝ)*base72 + (85070076604451/8871000000000000000000000000 : ℝ)*base74 + (1381928624785219239/369625000000000000000000000000000 : ℝ)*base76 + (1235699650706719239/369625000000000000000000000000000 : ℝ)*base78 + (3772925468346719239/369625000000000000000000000000000 : ℝ)*base80 + (1719861944183/2217750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (28252679/2000000000000000000000 : ℝ)*base89 + (28252679/2000000000000000000000 : ℝ)*base91 + (28252679/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-11617/12500 : ℝ) ≤ (-549610316436372721582170719/591400000000000000000000000 : ℝ) := by norm_num
    linear_combination (48430547/100000000000000 : ℝ)*(lower1) + (15373637/100000000000000 : ℝ)*(lower2) + (22125691/100000000000000 : ℝ)*(lower3) + (17392677/100000000000000 : ℝ)*(upper5) + (597513432583801/50000000000000 : ℝ)*(major0) + (597513432583801/50000000000000 : ℝ)*(major1) + (597513432583801/50000000000000 : ℝ)*(major2) + (27621188711/100000000000000 : ℝ)*(sp5) + (505079181/20000000000000 : ℝ)*(sp6) + (1916656101/100000000000000 : ℝ)*(sp7) + (93340238658409/5000000000000 : ℝ)*(sp12) + (466694287994867/25000000000000 : ℝ)*(sp13) + (933401123886137/50000000000000 : ℝ)*(sp14) + (554224963881247/100000000000000 : ℝ)*(sp15) + (138556720134337/25000000000000 : ℝ)*(f.failure) + (93340238658409/5000000000000 : ℝ)*(f.sum) + (39887921453447/8871000000000000000000000000 : ℝ)*base65 + (1654040215891427581/184812500000000000000000000000000 : ℝ)*base68 + (630822630866427581/184812500000000000000000000000000 : ℝ)*base70 + (429182709528177581/184812500000000000000000000000000 : ℝ)*base72 + (37318436933023/8871000000000000000000000000 : ℝ)*base74 + (100218626800509919/184812500000000000000000000000000 : ℝ)*base75 + (170999015869634919/184812500000000000000000000000000 : ℝ)*base77 + (75424310245197419/184812500000000000000000000000000 : ℝ)*base79 + (7991566641859/8871000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3392229/2500000000000000000000 : ℝ)*base89 + (3392229/2500000000000000000000 : ℝ)*base91 + (3392229/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1752_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1121/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1813/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68951/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58211/100000 : ℝ) else (40841/50000 : ℝ) ≤ X j i ∧ X j i ≤ (11617/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1752_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1752_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1813/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68951/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58211/100000 : ℝ) else (40841/50000 : ℝ) ≤ X j i ∧ X j i ≤ (11617/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1752_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1752_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5791/1024 : ℝ) ≤ p) (hpb : p ≤ (5807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (215620517/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1813/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68951/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58211/100000 : ℝ) else (40841/50000 : ℝ) ≤ X j i ∧ X j i ≤ (11617/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1752_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

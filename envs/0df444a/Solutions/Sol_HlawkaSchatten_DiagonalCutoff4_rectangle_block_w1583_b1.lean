-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1583_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:46.789644+00:00
-- url     : https://prove2.me/submissions/61ccc5bc-cb5a-4a6e-9ca3-b6b2846d8282

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
theorem support_rectangle_w1583_s3_0 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1767791513/10000000000 : ℝ)*x 0 + (271279179/500000000 : ℝ)*x 1 + (5219187321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1767791513/10000000000 : ℝ)^4663 ≤ (10855783159983/100000000000000 : ℝ)^3639 := by
    have hnat : (1767791513 : ℕ)^4663*100000000000000^3639 ≤ 10855783159983^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767791513 10000000000 10855783159983 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271279179/500000000 : ℝ)^4663 ≤ (22839719248581/50000000000000 : ℝ)^3639 := by
    have hnat : (271279179 : ℕ)^4663*50000000000000^3639 ≤ 22839719248581^3639*500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271279179 500000000 22839719248581 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219187321/10000000000 : ℝ)^4663 ≤ (21732389160577/50000000000000 : ℝ)^3639 := by
    have hnat : (5219187321 : ℕ)^4663*50000000000000^3639 ≤ 21732389160577^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219187321 10000000000 21732389160577 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1767791513/10000000000 : ℝ), (271279179/500000000 : ℝ), (5219187321/10000000000 : ℝ)] ![(10855783159983/100000000000000 : ℝ), (22839719248581/50000000000000 : ℝ), (21732389160577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1767791513/10000000000 : ℝ)|^4663 ≤ (10855783159983/100000000000000 : ℝ)^3639
        have hw : |(-1767791513/10000000000 : ℝ)|=(1767791513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271279179/500000000 : ℝ)|^4663 ≤ (22839719248581/50000000000000 : ℝ)^3639
        have hw : |(271279179/500000000 : ℝ)|=(271279179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219187321/10000000000 : ℝ)|^4663 ≤ (21732389160577/50000000000000 : ℝ)^3639
        have hw : |(5219187321/10000000000 : ℝ)|=(5219187321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s3_1 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534776731/1000000000 : ℝ)*x 0 + (-1873387779/10000000000 : ℝ)*x 1 + (2609593797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534776731/1000000000 : ℝ)^4663 ≤ (44841624214513/100000000000000 : ℝ)^3639 := by
    have hnat : (534776731 : ℕ)^4663*100000000000000^3639 ≤ 44841624214513^3639*1000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534776731 1000000000 44841624214513 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1873387779/10000000000 : ℝ)^4663 ≤ (5846797267889/50000000000000 : ℝ)^3639 := by
    have hnat : (1873387779 : ℕ)^4663*50000000000000^3639 ≤ 5846797267889^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873387779 10000000000 5846797267889 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609593797/5000000000 : ℝ)^4663 ≤ (43464781234423/100000000000000 : ℝ)^3639 := by
    have hnat : (2609593797 : ℕ)^4663*100000000000000^3639 ≤ 43464781234423^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609593797 5000000000 43464781234423 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534776731/1000000000 : ℝ), (-1873387779/10000000000 : ℝ), (2609593797/5000000000 : ℝ)] ![(44841624214513/100000000000000 : ℝ), (5846797267889/50000000000000 : ℝ), (43464781234423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534776731/1000000000 : ℝ)|^4663 ≤ (44841624214513/100000000000000 : ℝ)^3639
        have hw : |(534776731/1000000000 : ℝ)|=(534776731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1873387779/10000000000 : ℝ)|^4663 ≤ (5846797267889/50000000000000 : ℝ)^3639
        have hw : |(-1873387779/10000000000 : ℝ)|=(1873387779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609593797/5000000000 : ℝ)|^4663 ≤ (43464781234423/100000000000000 : ℝ)^3639
        have hw : |(2609593797/5000000000 : ℝ)|=(2609593797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s3_2 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347767251/10000000000 : ℝ)*x 0 + (1043837511/2000000000 : ℝ)*x 1 + (-187338791/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347767251/10000000000 : ℝ)^4663 ≤ (44841623580579/100000000000000 : ℝ)^3639 := by
    have hnat : (5347767251 : ℕ)^4663*100000000000000^3639 ≤ 44841623580579^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347767251 10000000000 44841623580579 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043837511/2000000000 : ℝ)^4663 ≤ (21732390409121/50000000000000 : ℝ)^3639 := by
    have hnat : (1043837511 : ℕ)^4663*50000000000000^3639 ≤ 21732390409121^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043837511 2000000000 21732390409121 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187338791/1000000000 : ℝ)^4663 ≤ (1169359558357/10000000000000 : ℝ)^3639 := by
    have hnat : (187338791 : ℕ)^4663*10000000000000^3639 ≤ 1169359558357^3639*1000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187338791 1000000000 1169359558357 10000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347767251/10000000000 : ℝ), (1043837511/2000000000 : ℝ), (-187338791/1000000000 : ℝ)] ![(44841623580579/100000000000000 : ℝ), (21732390409121/50000000000000 : ℝ), (1169359558357/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347767251/10000000000 : ℝ)|^4663 ≤ (44841623580579/100000000000000 : ℝ)^3639
        have hw : |(5347767251/10000000000 : ℝ)|=(5347767251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043837511/2000000000 : ℝ)|^4663 ≤ (21732390409121/50000000000000 : ℝ)^3639
        have hw : |(1043837511/2000000000 : ℝ)|=(1043837511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187338791/1000000000 : ℝ)|^4663 ≤ (1169359558357/10000000000000 : ℝ)^3639
        have hw : |(-187338791/1000000000 : ℝ)|=(187338791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s3_3 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237680873/10000000000 : ℝ)*x 0 + (1998814623/5000000000 : ℝ)*x 1 + (4489156679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237680873/10000000000 : ℝ)^4663 ≤ (33281556822559/100000000000000 : ℝ)^3639 := by
    have hnat : (4237680873 : ℕ)^4663*100000000000000^3639 ≤ 33281556822559^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237680873 10000000000 33281556822559 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1998814623/5000000000 : ℝ)^4663 ≤ (30885265471293/100000000000000 : ℝ)^3639 := by
    have hnat : (1998814623 : ℕ)^4663*100000000000000^3639 ≤ 30885265471293^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998814623 5000000000 30885265471293 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489156679/10000000000 : ℝ)^4663 ≤ (35833177693031/100000000000000 : ℝ)^3639 := by
    have hnat : (4489156679 : ℕ)^4663*100000000000000^3639 ≤ 35833177693031^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489156679 10000000000 35833177693031 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237680873/10000000000 : ℝ), (1998814623/5000000000 : ℝ), (4489156679/10000000000 : ℝ)] ![(33281556822559/100000000000000 : ℝ), (30885265471293/100000000000000 : ℝ), (35833177693031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237680873/10000000000 : ℝ)|^4663 ≤ (33281556822559/100000000000000 : ℝ)^3639
        have hw : |(4237680873/10000000000 : ℝ)|=(4237680873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1998814623/5000000000 : ℝ)|^4663 ≤ (30885265471293/100000000000000 : ℝ)^3639
        have hw : |(1998814623/5000000000 : ℝ)|=(1998814623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489156679/10000000000 : ℝ)|^4663 ≤ (35833177693031/100000000000000 : ℝ)^3639
        have hw : |(4489156679/10000000000 : ℝ)|=(4489156679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s3_4 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-883909531/5000000000 : ℝ)*x 0 + (2610139999/5000000000 : ℝ)*x 1 + (2712241303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (883909531/5000000000 : ℝ)^4663 ≤ (1085599994051/10000000000000 : ℝ)^3639 := by
    have hnat : (883909531 : ℕ)^4663*10000000000000^3639 ≤ 1085599994051^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883909531 5000000000 1085599994051 10000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610139999/5000000000 : ℝ)^4663 ≤ (43476438965193/100000000000000 : ℝ)^3639 := by
    have hnat : (2610139999 : ℕ)^4663*100000000000000^3639 ≤ 43476438965193^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610139999 5000000000 43476438965193 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712241303/5000000000 : ℝ)^4663 ≤ (356777820871/781250000000 : ℝ)^3639 := by
    have hnat : (2712241303 : ℕ)^4663*781250000000^3639 ≤ 356777820871^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712241303 5000000000 356777820871 781250000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-883909531/5000000000 : ℝ), (2610139999/5000000000 : ℝ), (2712241303/5000000000 : ℝ)] ![(1085599994051/10000000000000 : ℝ), (43476438965193/100000000000000 : ℝ), (356777820871/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-883909531/5000000000 : ℝ)|^4663 ≤ (1085599994051/10000000000000 : ℝ)^3639
        have hw : |(-883909531/5000000000 : ℝ)|=(883909531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610139999/5000000000 : ℝ)|^4663 ≤ (43476438965193/100000000000000 : ℝ)^3639
        have hw : |(2610139999/5000000000 : ℝ)|=(2610139999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712241303/5000000000 : ℝ)|^4663 ≤ (356777820871/781250000000 : ℝ)^3639
        have hw : |(2712241303/5000000000 : ℝ)|=(2712241303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s3_5 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661634769/1250000000 : ℝ)*x 0 + (-1668092841/10000000000 : ℝ)*x 1 + (5424483187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661634769/1250000000 : ℝ)^4663 ≤ (8850971207097/20000000000000 : ℝ)^3639 := by
    have hnat : (661634769 : ℕ)^4663*20000000000000^3639 ≤ 8850971207097^3639*1250000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661634769 1250000000 8850971207097 20000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1668092841/10000000000 : ℝ)^4663 ≤ (1259697076663/12500000000000 : ℝ)^3639 := by
    have hnat : (1668092841 : ℕ)^4663*12500000000000^3639 ≤ 1259697076663^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668092841 10000000000 1259697076663 12500000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424483187/10000000000 : ℝ)^4663 ≤ (45667567339199/100000000000000 : ℝ)^3639 := by
    have hnat : (5424483187 : ℕ)^4663*100000000000000^3639 ≤ 45667567339199^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424483187 10000000000 45667567339199 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661634769/1250000000 : ℝ), (-1668092841/10000000000 : ℝ), (5424483187/10000000000 : ℝ)] ![(8850971207097/20000000000000 : ℝ), (1259697076663/12500000000000 : ℝ), (45667567339199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661634769/1250000000 : ℝ)|^4663 ≤ (8850971207097/20000000000000 : ℝ)^3639
        have hw : |(661634769/1250000000 : ℝ)|=(661634769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1668092841/10000000000 : ℝ)|^4663 ≤ (1259697076663/12500000000000 : ℝ)^3639
        have hw : |(-1668092841/10000000000 : ℝ)|=(1668092841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424483187/10000000000 : ℝ)|^4663 ≤ (45667567339199/100000000000000 : ℝ)^3639
        have hw : |(5424483187/10000000000 : ℝ)|=(5424483187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s3_6 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293078633/10000000000 : ℝ)*x 0 + (5424482509/10000000000 : ℝ)*x 1 + (-5212791/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293078633/10000000000 : ℝ)^4663 ≤ (44254861188733/100000000000000 : ℝ)^3639 := by
    have hnat : (5293078633 : ℕ)^4663*100000000000000^3639 ≤ 44254861188733^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293078633 10000000000 44254861188733 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424482509/10000000000 : ℝ)^4663 ≤ (45667560025071/100000000000000 : ℝ)^3639 := by
    have hnat : (5424482509 : ℕ)^4663*100000000000000^3639 ≤ 45667560025071^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424482509 10000000000 45667560025071 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212791/31250000 : ℝ)^4663 ≤ (10077578773153/100000000000000 : ℝ)^3639 := by
    have hnat : (5212791 : ℕ)^4663*100000000000000^3639 ≤ 10077578773153^3639*31250000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212791 31250000 10077578773153 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293078633/10000000000 : ℝ), (5424482509/10000000000 : ℝ), (-5212791/31250000 : ℝ)] ![(44254861188733/100000000000000 : ℝ), (45667560025071/100000000000000 : ℝ), (10077578773153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293078633/10000000000 : ℝ)|^4663 ≤ (44254861188733/100000000000000 : ℝ)^3639
        have hw : |(5293078633/10000000000 : ℝ)|=(5293078633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424482509/10000000000 : ℝ)|^4663 ≤ (45667560025071/100000000000000 : ℝ)^3639
        have hw : |(5424482509/10000000000 : ℝ)|=(5424482509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5212791/31250000 : ℝ)|^4663 ≤ (10077578773153/100000000000000 : ℝ)^3639
        have hw : |(-5212791/31250000 : ℝ)|=(5212791/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s3_7 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33901971/80000000 : ℝ)*x 0 + (56081941/125000000 : ℝ)*x 1 + (4000249887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33901971/80000000 : ℝ)^4663 ≤ (8320554004521/25000000000000 : ℝ)^3639 := by
    have hnat : (33901971 : ℕ)^4663*25000000000000^3639 ≤ 8320554004521^3639*80000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33901971 80000000 8320554004521 25000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56081941/125000000 : ℝ)^4663 ≤ (8951642986257/25000000000000 : ℝ)^3639 := by
    have hnat : (56081941 : ℕ)^4663*25000000000000^3639 ≤ 8951642986257^3639*125000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56081941 125000000 8951642986257 25000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4000249887/10000000000 : ℝ)^4663 ≤ (30911212029961/100000000000000 : ℝ)^3639 := by
    have hnat : (4000249887 : ℕ)^4663*100000000000000^3639 ≤ 30911212029961^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4000249887 10000000000 30911212029961 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33901971/80000000 : ℝ), (56081941/125000000 : ℝ), (4000249887/10000000000 : ℝ)] ![(8320554004521/25000000000000 : ℝ), (8951642986257/25000000000000 : ℝ), (30911212029961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33901971/80000000 : ℝ)|^4663 ≤ (8320554004521/25000000000000 : ℝ)^3639
        have hw : |(33901971/80000000 : ℝ)|=(33901971/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56081941/125000000 : ℝ)|^4663 ≤ (8951642986257/25000000000000 : ℝ)^3639
        have hw : |(56081941/125000000 : ℝ)|=(56081941/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4000249887/10000000000 : ℝ)|^4663 ≤ (30911212029961/100000000000000 : ℝ)^3639
        have hw : |(4000249887/10000000000 : ℝ)|=(4000249887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1583_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2227/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7757/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10891/100000 : ℝ) ^ (4661/1024 : ℝ) ≤ (129364664473519/3125000000000000000 : ℝ) := by
    have hpowers : (10891/100000 : ℝ)^4661 ≤ (129364664473519/3125000000000000000 : ℝ)^1024 := by
      have hnat : (10891 : ℕ)^4661*3125000000000000000^1024 ≤ 129364664473519^1024*100000^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10891 100000 129364664473519 3125000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10891/100000 : ℝ)) (X := (129364664473519/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15779/100000 : ℝ) ^ (4661/1024 : ℝ) ≤ (22379583032084567/100000000000000000000 : ℝ) := by
    have hpowers : (15779/100000 : ℝ)^4661 ≤ (22379583032084567/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15779 : ℕ)^4661*100000000000000000000^1024 ≤ 22379583032084567^1024*100000^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15779 100000 22379583032084567 100000000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15779/100000 : ℝ)) (X := (22379583032084567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562629364664473519/1562500000000000000 : ℝ) ≤ (10000181887337619/10000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (1562629364664473519/1562500000000000000 : ℝ)^1024 ≤ (10000181887337619/10000000000000000 : ℝ)^4661 := by
      have hnat : (1562629364664473519 : ℕ)^1024*10000000000000000^4661 ≤ 10000181887337619^4661*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562629364664473519 1562500000000000000 10000181887337619 10000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000181887337619/10000000000000000 : ℝ)) (X := (1562629364664473519/1562500000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001060770091809487/4000000000000000000 : ℝ) ≤ (5000291277677681/5000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (4001060770091809487/4000000000000000000 : ℝ)^1024 ≤ (5000291277677681/5000000000000000 : ℝ)^4661 := by
      have hnat : (4001060770091809487 : ℕ)^1024*5000000000000000^4661 ≤ 5000291277677681^4661*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001060770091809487 4000000000000000000 5000291277677681 5000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000291277677681/5000000000000000 : ℝ)) (X := (4001060770091809487/4000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022379583032084567/50000000000000000000 : ℝ) ≤ (2000196644674621/2000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (50022379583032084567/50000000000000000000 : ℝ)^1024 ≤ (2000196644674621/2000000000000000 : ℝ)^4661 := by
      have hnat : (50022379583032084567 : ℕ)^1024*2000000000000000^4661 ≤ 2000196644674621^4661*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022379583032084567 50000000000000000000 2000196644674621 2000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000196644674621/2000000000000000 : ℝ)) (X := (50022379583032084567/50000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(129364664473519/3125000000000000000 : ℝ) ≤ ((24436080857271901823/24440000000000000000 : ℝ)+2*(400668017743/488800000000000 : ℝ)*(10891/100000 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (24436080857271901823/24440000000000000000 : ℝ)+2*(400668017743/488800000000000 : ℝ)*(10891/100000 : ℝ)=(10000181887337619/10000000000000000 : ℝ) by norm_num, show 1+2*(129364664473519/3125000000000000000 : ℝ)=(1562629364664473519/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22379583032084567/100000000000000000000 : ℝ)+(129364664473519/3125000000000000000 : ℝ) ≤ ((24436080857271901823/24440000000000000000 : ℝ)+(400668017743/488800000000000 : ℝ)*((15779/100000 : ℝ)+(10891/100000 : ℝ)))^(4661/1024 : ℝ) := by
    rw [show (24436080857271901823/24440000000000000000 : ℝ)+(400668017743/488800000000000 : ℝ)*((15779/100000 : ℝ)+(10891/100000 : ℝ))=(5000291277677681/5000000000000000 : ℝ) by norm_num, show 1+(22379583032084567/100000000000000000000 : ℝ)+(129364664473519/3125000000000000000 : ℝ)=(4001060770091809487/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22379583032084567/100000000000000000000 : ℝ) ≤ ((24436080857271901823/24440000000000000000 : ℝ)+2*(400668017743/488800000000000 : ℝ)*(15779/100000 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (24436080857271901823/24440000000000000000 : ℝ)+2*(400668017743/488800000000000 : ℝ)*(15779/100000 : ℝ)=(2000196644674621/2000000000000000 : ℝ) by norm_num, show 1+2*(22379583032084567/100000000000000000000 : ℝ)=(50022379583032084567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24436080857271901823/24440000000000000000 : ℝ)*(X 1 0+X 2 0)+(400668017743/488800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (10891/100000 : ℝ)) (hi := (15779/100000 : ℝ)) (c := (24436080857271901823/24440000000000000000 : ℝ)) (alpha := (400668017743/488800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24436080857271901823/24440000000000000000 : ℝ)*(X 0 1+X 2 1)+(400668017743/488800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (10891/100000 : ℝ)) (hi := (15779/100000 : ℝ)) (c := (24436080857271901823/24440000000000000000 : ℝ)) (alpha := (400668017743/488800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24436080857271901823/24440000000000000000 : ℝ)*(X 0 2+X 1 2)+(400668017743/488800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (10891/100000 : ℝ)) (hi := (15779/100000 : ℝ)) (c := (24436080857271901823/24440000000000000000 : ℝ)) (alpha := (400668017743/488800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1767791513/10000000000 : ℝ)*X 0 0+(271279179/500000000 : ℝ)*X 0 1+(5219187321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534776731/1000000000 : ℝ)*X 1 0+(-1873387779/10000000000 : ℝ)*X 1 1+(2609593797/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347767251/10000000000 : ℝ)*X 2 0+(1043837511/2000000000 : ℝ)*X 2 1+(-187338791/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4237680873/10000000000 : ℝ)*X 0 0+(1998814623/5000000000 : ℝ)*X 0 1+(4489156679/10000000000 : ℝ)*X 0 2+(4237680873/10000000000 : ℝ)*X 1 0+(1998814623/5000000000 : ℝ)*X 1 1+(4489156679/10000000000 : ℝ)*X 1 2+(4237680873/10000000000 : ℝ)*X 2 0+(1998814623/5000000000 : ℝ)*X 2 1+(4489156679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-883909531/5000000000 : ℝ)*X 0 0+(2610139999/5000000000 : ℝ)*X 0 1+(2712241303/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661634769/1250000000 : ℝ)*X 1 0+(-1668092841/10000000000 : ℝ)*X 1 1+(5424483187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293078633/10000000000 : ℝ)*X 2 0+(5424482509/10000000000 : ℝ)*X 2 1+(-5212791/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33901971/80000000 : ℝ)*X 0 0+(56081941/125000000 : ℝ)*X 0 1+(4000249887/10000000000 : ℝ)*X 0 2+(33901971/80000000 : ℝ)*X 1 0+(56081941/125000000 : ℝ)*X 1 1+(4000249887/10000000000 : ℝ)*X 1 2+(33901971/80000000 : ℝ)*X 2 0+(56081941/125000000 : ℝ)*X 2 1+(4000249887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3713359729628546277981225921/611000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248628157/25000000000000 : ℝ)*(base19) + (467975567/50000000000000 : ℝ)*(base23) + (48207807/100000000000000 : ℝ)*(lower2) + (143713791/100000000000000 : ℝ)*(upper3) + (45476559/100000000000000 : ℝ)*(lower4) + (1719897096444309/50000000000000 : ℝ)*(major0) + (1719897096444309/50000000000000 : ℝ)*(major1) + (1719897096444309/50000000000000 : ℝ)*(major2) + (2422538054972427/50000000000000 : ℝ)*(sp0) + (2422548858882531/50000000000000 : ℝ)*(sp1) + (1211274444081639/25000000000000 : ℝ)*(sp2) + (20344812079221/1000000000000 : ℝ)*(sp3) + (5650583209/25000000000000 : ℝ)*(sp4) + (8262993711/100000000000000 : ℝ)*(sp7) + (508622367728953/25000000000000 : ℝ)*(f.failure) + (484509871227769/10000000000000 : ℝ)*(f.sum) + (23042709855433/12220000000000000000000000000 : ℝ)*base66 + (2206136428651574693/1222000000000000000000000000000000 : ℝ)*base68 + (8497018064989574693/1222000000000000000000000000000000 : ℝ)*base70 + (7949624189025574693/1222000000000000000000000000000000 : ℝ)*base72 + (44581470046547/12220000000000000000000000000 : ℝ)*base73 + (7283408371694425307/1222000000000000000000000000000000 : ℝ)*base75 + (1148820667617574693/1222000000000000000000000000000000 : ℝ)*base78 + (12196479076444425307/1222000000000000000000000000000000 : ℝ)*base79 + (54183637919247/12220000000000000000000000000 : ℝ)*base81 + (3250827/312500000000000000000 : ℝ)*base89 + (3250827/312500000000000000000 : ℝ)*base91 + (3250827/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (118626898275266934595107699/9400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (634251589/50000000000000 : ℝ)*(base19) + (1931400661/100000000000000 : ℝ)*(base23) + (329295597/100000000000000 : ℝ)*(upper3) + (27796593/25000000000000 : ℝ)*(lower4) + (212974361/100000000000000 : ℝ)*(upper5) + (347670827365277/10000000000000 : ℝ)*(major0) + (347670827365277/10000000000000 : ℝ)*(major1) + (347670827365277/10000000000000 : ℝ)*(major2) + (815335483/3125000000000 : ℝ)*(sp1) + (13424033989/50000000000000 : ℝ)*(sp2) + (4897093573736633/100000000000000 : ℝ)*(sp4) + (2448533107248999/50000000000000 : ℝ)*(sp5) + (2448532397133997/50000000000000 : ℝ)*(sp6) + (2056322552906143/100000000000000 : ℝ)*(sp7) + (2056322552906143/100000000000000 : ℝ)*(f.failure) + (4897093573736633/100000000000000 : ℝ)*(f.sum) + (45686013361/37600000000000000000000000 : ℝ)*base66 + (119565278613219233/18800000000000000000000000000000 : ℝ)*base68 + (37798059684780767/18800000000000000000000000000000 : ℝ)*base69 + (41264718735180767/18800000000000000000000000000000 : ℝ)*base71 + (1192433365177/188000000000000000000000000 : ℝ)*base74 + (1066866115180767/18800000000000000000000000000000 : ℝ)*base75 + (23008459403980767/18800000000000000000000000000000 : ℝ)*base77 + (121696521850819233/18800000000000000000000000000000 : ℝ)*base80 + (493861195219/188000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3853037/1250000000000000000000 : ℝ)*base89 + (3853037/1250000000000000000000 : ℝ)*base91 + (3853037/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1583_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2227/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7757/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1583_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1583_s4_0 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-883992969/5000000000 : ℝ)*x 0 + (5424279747/10000000000 : ℝ)*x 1 + (5220362011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (883992969/5000000000 : ℝ)^4663 ≤ (5428656546299/50000000000000 : ℝ)^3639 := by
    have hnat : (883992969 : ℕ)^4663*50000000000000^3639 ≤ 5428656546299^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883992969 5000000000 5428656546299 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424279747/10000000000 : ℝ)^4663 ≤ (45665372680829/100000000000000 : ℝ)^3639 := by
    have hnat : (5424279747 : ℕ)^4663*100000000000000^3639 ≤ 45665372680829^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424279747 10000000000 45665372680829 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220362011/10000000000 : ℝ)^4663 ≤ (173909256821/400000000000 : ℝ)^3639 := by
    have hnat : (5220362011 : ℕ)^4663*400000000000^3639 ≤ 173909256821^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220362011 10000000000 173909256821 400000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-883992969/5000000000 : ℝ), (5424279747/10000000000 : ℝ), (5220362011/10000000000 : ℝ)] ![(5428656546299/50000000000000 : ℝ), (45665372680829/100000000000000 : ℝ), (173909256821/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-883992969/5000000000 : ℝ)|^4663 ≤ (5428656546299/50000000000000 : ℝ)^3639
        have hw : |(-883992969/5000000000 : ℝ)|=(883992969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424279747/10000000000 : ℝ)|^4663 ≤ (45665372680829/100000000000000 : ℝ)^3639
        have hw : |(5424279747/10000000000 : ℝ)|=(5424279747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220362011/10000000000 : ℝ)|^4663 ≤ (173909256821/400000000000 : ℝ)^3639
        have hw : |(5220362011/10000000000 : ℝ)|=(5220362011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s4_1 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069484169/2000000000 : ℝ)*x 0 + (-1872286453/10000000000 : ℝ)*x 1 + (2610180901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069484169/2000000000 : ℝ)^4663 ≤ (5604737700497/12500000000000 : ℝ)^3639 := by
    have hnat : (1069484169 : ℕ)^4663*12500000000000^3639 ≤ 5604737700497^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069484169 2000000000 5604737700497 12500000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1872286453/10000000000 : ℝ)^4663 ≤ (11684786406673/100000000000000 : ℝ)^3639 := by
    have hnat : (1872286453 : ℕ)^4663*100000000000000^3639 ≤ 11684786406673^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872286453 10000000000 11684786406673 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610180901/5000000000 : ℝ)^4663 ≤ (10869327993701/25000000000000 : ℝ)^3639 := by
    have hnat : (2610180901 : ℕ)^4663*25000000000000^3639 ≤ 10869327993701^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610180901 5000000000 10869327993701 25000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069484169/2000000000 : ℝ), (-1872286453/10000000000 : ℝ), (2610180901/5000000000 : ℝ)] ![(5604737700497/12500000000000 : ℝ), (11684786406673/100000000000000 : ℝ), (10869327993701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069484169/2000000000 : ℝ)|^4663 ≤ (5604737700497/12500000000000 : ℝ)^3639
        have hw : |(1069484169/2000000000 : ℝ)|=(1069484169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1872286453/10000000000 : ℝ)|^4663 ≤ (11684786406673/100000000000000 : ℝ)^3639
        have hw : |(-1872286453/10000000000 : ℝ)|=(1872286453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610180901/5000000000 : ℝ)|^4663 ≤ (10869327993701/25000000000000 : ℝ)^3639
        have hw : |(2610180901/5000000000 : ℝ)|=(2610180901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s4_2 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347421039/10000000000 : ℝ)*x 0 + (5220361581/10000000000 : ℝ)*x 1 + (-936143243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347421039/10000000000 : ℝ)^4663 ≤ (44837903688399/100000000000000 : ℝ)^3639 := by
    have hnat : (5347421039 : ℕ)^4663*100000000000000^3639 ≤ 44837903688399^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347421039 10000000000 44837903688399 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220361581/10000000000 : ℝ)^4663 ≤ (21738654808147/50000000000000 : ℝ)^3639 := by
    have hnat : (5220361581 : ℕ)^4663*50000000000000^3639 ≤ 21738654808147^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220361581 10000000000 21738654808147 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (936143243/5000000000 : ℝ)^4663 ≤ (11684786670577/100000000000000 : ℝ)^3639 := by
    have hnat : (936143243 : ℕ)^4663*100000000000000^3639 ≤ 11684786670577^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936143243 5000000000 11684786670577 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347421039/10000000000 : ℝ), (5220361581/10000000000 : ℝ), (-936143243/5000000000 : ℝ)] ![(44837903688399/100000000000000 : ℝ), (21738654808147/50000000000000 : ℝ), (11684786670577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347421039/10000000000 : ℝ)|^4663 ≤ (44837903688399/100000000000000 : ℝ)^3639
        have hw : |(5347421039/10000000000 : ℝ)|=(5347421039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220361581/10000000000 : ℝ)|^4663 ≤ (21738654808147/50000000000000 : ℝ)^3639
        have hw : |(5220361581/10000000000 : ℝ)|=(5220361581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-936143243/5000000000 : ℝ)|^4663 ≤ (11684786670577/100000000000000 : ℝ)^3639
        have hw : |(-936143243/5000000000 : ℝ)|=(936143243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s4_3 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237803787/10000000000 : ℝ)*x 0 + (800113167/2000000000 : ℝ)*x 1 + (4486192863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237803787/10000000000 : ℝ)^4663 ≤ (33282793800257/100000000000000 : ℝ)^3639 := by
    have hnat : (4237803787 : ℕ)^4663*100000000000000^3639 ≤ 33282793800257^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237803787 10000000000 33282793800257 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (800113167/2000000000 : ℝ)^4663 ≤ (15457170252553/50000000000000 : ℝ)^3639 := by
    have hnat : (800113167 : ℕ)^4663*50000000000000^3639 ≤ 15457170252553^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800113167 2000000000 15457170252553 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486192863/10000000000 : ℝ)^4663 ≤ (35802865677999/100000000000000 : ℝ)^3639 := by
    have hnat : (4486192863 : ℕ)^4663*100000000000000^3639 ≤ 35802865677999^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486192863 10000000000 35802865677999 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237803787/10000000000 : ℝ), (800113167/2000000000 : ℝ), (4486192863/10000000000 : ℝ)] ![(33282793800257/100000000000000 : ℝ), (15457170252553/50000000000000 : ℝ), (35802865677999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237803787/10000000000 : ℝ)|^4663 ≤ (33282793800257/100000000000000 : ℝ)^3639
        have hw : |(4237803787/10000000000 : ℝ)|=(4237803787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(800113167/2000000000 : ℝ)|^4663 ≤ (15457170252553/50000000000000 : ℝ)^3639
        have hw : |(800113167/2000000000 : ℝ)|=(800113167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486192863/10000000000 : ℝ)|^4663 ≤ (35802865677999/100000000000000 : ℝ)^3639
        have hw : |(4486192863/10000000000 : ℝ)|=(4486192863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s4_4 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-353602539/2000000000 : ℝ)*x 0 + (5221428071/10000000000 : ℝ)*x 1 + (5423205543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353602539/2000000000 : ℝ)^4663 ≤ (10857523647453/100000000000000 : ℝ)^3639 := by
    have hnat : (353602539 : ℕ)^4663*100000000000000^3639 ≤ 10857523647453^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353602539 2000000000 10857523647453 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221428071/10000000000 : ℝ)^4663 ≤ (43488691514761/100000000000000 : ℝ)^3639 := by
    have hnat : (5221428071 : ℕ)^4663*100000000000000^3639 ≤ 43488691514761^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221428071 10000000000 43488691514761 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423205543/10000000000 : ℝ)^4663 ≤ (356670193973/781250000000 : ℝ)^3639 := by
    have hnat : (5423205543 : ℕ)^4663*781250000000^3639 ≤ 356670193973^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423205543 10000000000 356670193973 781250000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353602539/2000000000 : ℝ), (5221428071/10000000000 : ℝ), (5423205543/10000000000 : ℝ)] ![(10857523647453/100000000000000 : ℝ), (43488691514761/100000000000000 : ℝ), (356670193973/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353602539/2000000000 : ℝ)|^4663 ≤ (10857523647453/100000000000000 : ℝ)^3639
        have hw : |(-353602539/2000000000 : ℝ)|=(353602539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221428071/10000000000 : ℝ)|^4663 ≤ (43488691514761/100000000000000 : ℝ)^3639
        have hw : |(5221428071/10000000000 : ℝ)|=(5221428071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423205543/10000000000 : ℝ)|^4663 ≤ (356670193973/781250000000 : ℝ)^3639
        have hw : |(5423205543/10000000000 : ℝ)|=(5423205543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s4_5 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646694533/5000000000 : ℝ)*x 0 + (-1669442447/10000000000 : ℝ)*x 1 + (542320577/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646694533/5000000000 : ℝ)^4663 ≤ (1770327483021/4000000000000 : ℝ)^3639 := by
    have hnat : (2646694533 : ℕ)^4663*4000000000000^3639 ≤ 1770327483021^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646694533 5000000000 1770327483021 4000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1669442447/10000000000 : ℝ)^4663 ≤ (403521025443/4000000000000 : ℝ)^3639 := by
    have hnat : (1669442447 : ℕ)^4663*4000000000000^3639 ≤ 403521025443^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669442447 10000000000 403521025443 4000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542320577/1000000000 : ℝ)^4663 ≤ (11413446819303/25000000000000 : ℝ)^3639 := by
    have hnat : (542320577 : ℕ)^4663*25000000000000^3639 ≤ 11413446819303^3639*1000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542320577 1000000000 11413446819303 25000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646694533/5000000000 : ℝ), (-1669442447/10000000000 : ℝ), (542320577/1000000000 : ℝ)] ![(1770327483021/4000000000000 : ℝ), (403521025443/4000000000000 : ℝ), (11413446819303/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646694533/5000000000 : ℝ)|^4663 ≤ (1770327483021/4000000000000 : ℝ)^3639
        have hw : |(2646694533/5000000000 : ℝ)|=(2646694533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1669442447/10000000000 : ℝ)|^4663 ≤ (403521025443/4000000000000 : ℝ)^3639
        have hw : |(-1669442447/10000000000 : ℝ)|=(1669442447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542320577/1000000000 : ℝ)|^4663 ≤ (11413446819303/25000000000000 : ℝ)^3639
        have hw : |(542320577/1000000000 : ℝ)|=(542320577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s4_6 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293388793/10000000000 : ℝ)*x 0 + (5423206037/10000000000 : ℝ)*x 1 + (-1669442453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293388793/10000000000 : ℝ)^4663 ≤ (44258184150661/100000000000000 : ℝ)^3639 := by
    have hnat : (5293388793 : ℕ)^4663*100000000000000^3639 ≤ 44258184150661^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293388793 10000000000 44258184150661 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423206037/10000000000 : ℝ)^4663 ≤ (11413447539341/25000000000000 : ℝ)^3639 := by
    have hnat : (5423206037 : ℕ)^4663*25000000000000^3639 ≤ 11413447539341^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423206037 10000000000 11413447539341 25000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1669442453/10000000000 : ℝ)^4663 ≤ (5044012841267/50000000000000 : ℝ)^3639 := by
    have hnat : (1669442453 : ℕ)^4663*50000000000000^3639 ≤ 5044012841267^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669442453 10000000000 5044012841267 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293388793/10000000000 : ℝ), (5423206037/10000000000 : ℝ), (-1669442453/10000000000 : ℝ)] ![(44258184150661/100000000000000 : ℝ), (11413447539341/25000000000000 : ℝ), (5044012841267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293388793/10000000000 : ℝ)|^4663 ≤ (44258184150661/100000000000000 : ℝ)^3639
        have hw : |(5293388793/10000000000 : ℝ)|=(5293388793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423206037/10000000000 : ℝ)|^4663 ≤ (11413447539341/25000000000000 : ℝ)^3639
        have hw : |(5423206037/10000000000 : ℝ)|=(5423206037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1669442453/10000000000 : ℝ)|^4663 ≤ (5044012841267/50000000000000 : ℝ)^3639
        have hw : |(-1669442453/10000000000 : ℝ)|=(1669442453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s4_7 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237866767/10000000000 : ℝ)*x 0 + (35869227/80000000 : ℝ)*x 1 + (50039051/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237866767/10000000000 : ℝ)^4663 ≤ (8320856905033/25000000000000 : ℝ)^3639 := by
    have hnat : (4237866767 : ℕ)^4663*25000000000000^3639 ≤ 8320856905033^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237866767 10000000000 8320856905033 25000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35869227/80000000 : ℝ)^4663 ≤ (35776897900661/100000000000000 : ℝ)^3639 := by
    have hnat : (35869227 : ℕ)^4663*100000000000000^3639 ≤ 35776897900661^3639*80000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35869227 80000000 35776897900661 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50039051/125000000 : ℝ)^4663 ≤ (309396744677/1000000000000 : ℝ)^3639 := by
    have hnat : (50039051 : ℕ)^4663*1000000000000^3639 ≤ 309396744677^3639*125000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50039051 125000000 309396744677 1000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237866767/10000000000 : ℝ), (35869227/80000000 : ℝ), (50039051/125000000 : ℝ)] ![(8320856905033/25000000000000 : ℝ), (35776897900661/100000000000000 : ℝ), (309396744677/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237866767/10000000000 : ℝ)|^4663 ≤ (8320856905033/25000000000000 : ℝ)^3639
        have hw : |(4237866767/10000000000 : ℝ)|=(4237866767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35869227/80000000 : ℝ)|^4663 ≤ (35776897900661/100000000000000 : ℝ)^3639
        have hw : |(35869227/80000000 : ℝ)|=(35869227/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50039051/125000000 : ℝ)|^4663 ≤ (309396744677/1000000000000 : ℝ)^3639
        have hw : |(50039051/125000000 : ℝ)|=(50039051/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1583_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7757/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2227/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (279/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7743/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7757/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2227/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7757/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2227/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7757/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2227/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7757/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2227/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7757/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2227/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7757/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2227/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2227/20000 : ℝ) ^ (4661/1024 : ℝ) ≤ (572367255640923/12500000000000000000 : ℝ) := by
    have hpowers : (2227/20000 : ℝ)^4661 ≤ (572367255640923/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2227 : ℕ)^4661*12500000000000000000^1024 ≤ 572367255640923^1024*20000^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2227 20000 572367255640923 12500000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2227/20000 : ℝ)) (X := (572367255640923/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7757/50000 : ℝ) ^ (4661/1024 : ℝ) ≤ (10359544966342079/50000000000000000000 : ℝ) := by
    have hpowers : (7757/50000 : ℝ)^4661 ≤ (10359544966342079/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7757 : ℕ)^4661*50000000000000000000^1024 ≤ 10359544966342079^1024*50000^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7757 50000 10359544966342079 50000000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7757/50000 : ℝ)) (X := (10359544966342079/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250572367255640923/6250000000000000000 : ℝ) ≤ (100002011870859/100000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (6250572367255640923/6250000000000000000 : ℝ)^1024 ≤ (100002011870859/100000000000000 : ℝ)^4661 := by
      have hnat : (6250572367255640923 : ℕ)^1024*100000000000000^4661 ≤ 100002011870859^4661*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250572367255640923 6250000000000000000 100002011870859 100000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100002011870859/100000000000000 : ℝ)) (X := (6250572367255640923/6250000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012649013988905771/50000000000000000000 : ℝ) ≤ (2000111146209697/2000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (50012649013988905771/50000000000000000000 : ℝ)^1024 ≤ (2000111146209697/2000000000000000 : ℝ)^4661 := by
      have hnat : (50012649013988905771 : ℕ)^1024*2000000000000000^4661 ≤ 2000111146209697^4661*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012649013988905771 50000000000000000000 2000111146209697 2000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000111146209697/2000000000000000 : ℝ)) (X := (50012649013988905771/50000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010359544966342079/25000000000000000000 : ℝ) ≤ (1000091027501107/1000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (25010359544966342079/25000000000000000000 : ℝ)^1024 ≤ (1000091027501107/1000000000000000 : ℝ)^4661 := by
      have hnat : (25010359544966342079 : ℕ)^1024*1000000000000000^4661 ≤ 1000091027501107^4661*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010359544966342079 25000000000000000000 1000091027501107 1000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000091027501107/1000000000000000 : ℝ)) (X := (25010359544966342079/25000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(572367255640923/12500000000000000000 : ℝ) ≤ ((875659706084047763/875800000000000000 : ℝ)+2*(70908792517/87580000000000 : ℝ)*(2227/20000 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (875659706084047763/875800000000000000 : ℝ)+2*(70908792517/87580000000000 : ℝ)*(2227/20000 : ℝ)=(100002011870859/100000000000000 : ℝ) by norm_num, show 1+2*(572367255640923/12500000000000000000 : ℝ)=(6250572367255640923/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10359544966342079/50000000000000000000 : ℝ)+(572367255640923/12500000000000000000 : ℝ) ≤ ((875659706084047763/875800000000000000 : ℝ)+(70908792517/87580000000000 : ℝ)*((7757/50000 : ℝ)+(2227/20000 : ℝ)))^(4661/1024 : ℝ) := by
    rw [show (875659706084047763/875800000000000000 : ℝ)+(70908792517/87580000000000 : ℝ)*((7757/50000 : ℝ)+(2227/20000 : ℝ))=(2000111146209697/2000000000000000 : ℝ) by norm_num, show 1+(10359544966342079/50000000000000000000 : ℝ)+(572367255640923/12500000000000000000 : ℝ)=(50012649013988905771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10359544966342079/50000000000000000000 : ℝ) ≤ ((875659706084047763/875800000000000000 : ℝ)+2*(70908792517/87580000000000 : ℝ)*(7757/50000 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (875659706084047763/875800000000000000 : ℝ)+2*(70908792517/87580000000000 : ℝ)*(7757/50000 : ℝ)=(1000091027501107/1000000000000000 : ℝ) by norm_num, show 1+2*(10359544966342079/50000000000000000000 : ℝ)=(25010359544966342079/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (875659706084047763/875800000000000000 : ℝ)*(X 1 0+X 2 0)+(70908792517/87580000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (2227/20000 : ℝ)) (hi := (7757/50000 : ℝ)) (c := (875659706084047763/875800000000000000 : ℝ)) (alpha := (70908792517/87580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (875659706084047763/875800000000000000 : ℝ)*(X 0 1+X 2 1)+(70908792517/87580000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (2227/20000 : ℝ)) (hi := (7757/50000 : ℝ)) (c := (875659706084047763/875800000000000000 : ℝ)) (alpha := (70908792517/87580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (875659706084047763/875800000000000000 : ℝ)*(X 0 2+X 1 2)+(70908792517/87580000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (2227/20000 : ℝ)) (hi := (7757/50000 : ℝ)) (c := (875659706084047763/875800000000000000 : ℝ)) (alpha := (70908792517/87580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-883992969/5000000000 : ℝ)*X 0 0+(5424279747/10000000000 : ℝ)*X 0 1+(5220362011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069484169/2000000000 : ℝ)*X 1 0+(-1872286453/10000000000 : ℝ)*X 1 1+(2610180901/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347421039/10000000000 : ℝ)*X 2 0+(5220361581/10000000000 : ℝ)*X 2 1+(-936143243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4237803787/10000000000 : ℝ)*X 0 0+(800113167/2000000000 : ℝ)*X 0 1+(4486192863/10000000000 : ℝ)*X 0 2+(4237803787/10000000000 : ℝ)*X 1 0+(800113167/2000000000 : ℝ)*X 1 1+(4486192863/10000000000 : ℝ)*X 1 2+(4237803787/10000000000 : ℝ)*X 2 0+(800113167/2000000000 : ℝ)*X 2 1+(4486192863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-353602539/2000000000 : ℝ)*X 0 0+(5221428071/10000000000 : ℝ)*X 0 1+(5423205543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646694533/5000000000 : ℝ)*X 1 0+(-1669442447/10000000000 : ℝ)*X 1 1+(542320577/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293388793/10000000000 : ℝ)*X 2 0+(5423206037/10000000000 : ℝ)*X 2 1+(-1669442453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4237866767/10000000000 : ℝ)*X 0 0+(35869227/80000000 : ℝ)*X 0 1+(50039051/125000000 : ℝ)*X 0 2+(4237866767/10000000000 : ℝ)*X 1 0+(35869227/80000000 : ℝ)*X 1 1+(50039051/125000000 : ℝ)*X 1 2+(4237866767/10000000000 : ℝ)*X 2 0+(35869227/80000000 : ℝ)*X 2 1+(50039051/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2709314734367154611686623/342109375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1215448949/100000000000000 : ℝ)*(base19) + (1282231319/100000000000000 : ℝ)*(base23) + (14856381/25000000000000 : ℝ)*(lower2) + (226746257/100000000000000 : ℝ)*(upper3) + (27945071/20000000000000 : ℝ)*(upper5) + (6799971696117/195312500000 : ℝ)*(major0) + (6799971696117/195312500000 : ℝ)*(major1) + (6799971696117/195312500000 : ℝ)*(major2) + (980790223579021/20000000000000 : ℝ)*(sp0) + (612995288887559/12500000000000 : ℝ)*(sp1) + (2451981122159051/50000000000000 : ℝ)*(sp2) + (514799861040579/25000000000000 : ℝ)*(sp3) + (3102163579/25000000000000 : ℝ)*(sp4) + (972766341/12500000000000 : ℝ)*(sp7) + (514801806573261/25000000000000 : ℝ)*(f.failure) + (4903963526549421/100000000000000 : ℝ)*(f.sum) + (1002952210857/2189500000000000000000000000 : ℝ)*base66 + (5900303721139711/2736875000000000000000000000000 : ℝ)*base67 + (29324978847489711/2736875000000000000000000000000 : ℝ)*base69 + (2858780806134291/684218750000000000000000000000 : ℝ)*base72 + (2180285801173/1094750000000000000000000000 : ℝ)*base73 + (1524936482563209/684218750000000000000000000000 : ℝ)*base75 + (2954972492050457/1368437500000000000000000000000 : ℝ)*base78 + (4313120549260793/1368437500000000000000000000000 : ℝ)*base79 + (1165593175429/273687500000000000000000000 : ℝ)*base81 + (448599/312500000000000000000 : ℝ)*base89 + (448599/312500000000000000000 : ℝ)*base91 + (448599/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76720881756493427494421499/21895000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152514137/25000000000000 : ℝ)*(base19) + (606447299/100000000000000 : ℝ)*(base23) + (120743227/100000000000000 : ℝ)*(upper2) + (11021321/6250000000000 : ℝ)*(upper3) + (48060681/25000000000000 : ℝ)*(upper5) + (1759247152855109/50000000000000 : ℝ)*(major0) + (1759247152855109/50000000000000 : ℝ)*(major1) + (1759247152855109/50000000000000 : ℝ)*(major2) + (10617485407/100000000000000 : ℝ)*(sp1) + (3239356059/25000000000000 : ℝ)*(sp2) + (4955951311277333/100000000000000 : ℝ)*(sp4) + (2477970041867689/50000000000000 : ℝ)*(sp5) + (2477968873702899/50000000000000 : ℝ)*(sp6) + (1040518591670939/50000000000000 : ℝ)*(sp7) + (1040518591670939/50000000000000 : ℝ)*(f.failure) + (4955951311277333/100000000000000 : ℝ)*(f.sum) + (8073536824117/4379000000000000000000000000 : ℝ)*base65 + (171088247983631167/43790000000000000000000000000000 : ℝ)*base67 + (78905628825508833/43790000000000000000000000000000 : ℝ)*base70 + (70997383852791167/43790000000000000000000000000000 : ℝ)*base71 + (12857021016679/4379000000000000000000000000 : ℝ)*base73 + (358377685137958833/43790000000000000000000000000000 : ℝ)*base76 + (264827812835341167/43790000000000000000000000000000 : ℝ)*base77 + (182348189677421167/43790000000000000000000000000000 : ℝ)*base79 + (5751252568811/1094750000000000000000000000 : ℝ)*base82 + (5099201/625000000000000000000 : ℝ)*base89 + (5099201/625000000000000000000 : ℝ)*base91 + (5099201/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1583_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7757/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2227/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1583_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1583_s5_0 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-884003143/5000000000 : ℝ)*x 0 + (2712075679/5000000000 : ℝ)*x 1 + (1305119197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (884003143/5000000000 : ℝ)^4663 ≤ (10857473213987/100000000000000 : ℝ)^3639 := by
    have hnat : (884003143 : ℕ)^4663*100000000000000^3639 ≤ 10857473213987^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884003143 5000000000 10857473213987 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712075679/5000000000 : ℝ)^4663 ≤ (9132797533051/20000000000000 : ℝ)^3639 := by
    have hnat : (2712075679 : ℕ)^4663*20000000000000^3639 ≤ 9132797533051^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712075679 5000000000 9132797533051 20000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305119197/2500000000 : ℝ)^4663 ≤ (43478539108141/100000000000000 : ℝ)^3639 := by
    have hnat : (1305119197 : ℕ)^4663*100000000000000^3639 ≤ 43478539108141^3639*2500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305119197 2500000000 43478539108141 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-884003143/5000000000 : ℝ), (2712075679/5000000000 : ℝ), (1305119197/2500000000 : ℝ)] ![(10857473213987/100000000000000 : ℝ), (9132797533051/20000000000000 : ℝ), (43478539108141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-884003143/5000000000 : ℝ)|^4663 ≤ (10857473213987/100000000000000 : ℝ)^3639
        have hw : |(-884003143/5000000000 : ℝ)|=(884003143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712075679/5000000000 : ℝ)|^4663 ≤ (9132797533051/20000000000000 : ℝ)^3639
        have hw : |(2712075679/5000000000 : ℝ)|=(2712075679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305119197/2500000000 : ℝ)|^4663 ≤ (43478539108141/100000000000000 : ℝ)^3639
        have hw : |(1305119197/2500000000 : ℝ)|=(1305119197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s5_1 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347386389/10000000000 : ℝ)*x 0 + (-468044827/2500000000 : ℝ)*x 1 + (261023839/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347386389/10000000000 : ℝ)^4663 ≤ (44837531393469/100000000000000 : ℝ)^3639 := by
    have hnat : (5347386389 : ℕ)^4663*100000000000000^3639 ≤ 44837531393469^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347386389 10000000000 44837531393469 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468044827/2500000000 : ℝ)^4663 ≤ (11683929565641/100000000000000 : ℝ)^3639 := by
    have hnat : (468044827 : ℕ)^4663*100000000000000^3639 ≤ 11683929565641^3639*2500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468044827 2500000000 11683929565641 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261023839/500000000 : ℝ)^4663 ≤ (8695707804553/20000000000000 : ℝ)^3639 := by
    have hnat : (261023839 : ℕ)^4663*20000000000000^3639 ≤ 8695707804553^3639*500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261023839 500000000 8695707804553 20000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347386389/10000000000 : ℝ), (-468044827/2500000000 : ℝ), (261023839/500000000 : ℝ)] ![(44837531393469/100000000000000 : ℝ), (11683929565641/100000000000000 : ℝ), (8695707804553/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347386389/10000000000 : ℝ)|^4663 ≤ (44837531393469/100000000000000 : ℝ)^3639
        have hw : |(5347386389/10000000000 : ℝ)|=(5347386389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-468044827/2500000000 : ℝ)|^4663 ≤ (11683929565641/100000000000000 : ℝ)^3639
        have hw : |(-468044827/2500000000 : ℝ)|=(468044827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261023839/500000000 : ℝ)|^4663 ≤ (8695707804553/20000000000000 : ℝ)^3639
        have hw : |(261023839/500000000 : ℝ)|=(261023839/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s5_2 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347386359/10000000000 : ℝ)*x 0 + (2610238403/5000000000 : ℝ)*x 1 + (-936089657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347386359/10000000000 : ℝ)^4663 ≤ (1401172845973/3125000000000 : ℝ)^3639 := by
    have hnat : (5347386359 : ℕ)^4663*3125000000000^3639 ≤ 1401172845973^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347386359 10000000000 1401172845973 3125000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610238403/5000000000 : ℝ)^4663 ≤ (21739269650119/50000000000000 : ℝ)^3639 := by
    have hnat : (2610238403 : ℕ)^4663*50000000000000^3639 ≤ 21739269650119^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610238403 5000000000 21739269650119 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (936089657/5000000000 : ℝ)^4663 ≤ (11683929613623/100000000000000 : ℝ)^3639 := by
    have hnat : (936089657 : ℕ)^4663*100000000000000^3639 ≤ 11683929613623^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936089657 5000000000 11683929613623 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347386359/10000000000 : ℝ), (2610238403/5000000000 : ℝ), (-936089657/5000000000 : ℝ)] ![(1401172845973/3125000000000 : ℝ), (21739269650119/50000000000000 : ℝ), (11683929613623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347386359/10000000000 : ℝ)|^4663 ≤ (1401172845973/3125000000000 : ℝ)^3639
        have hw : |(5347386359/10000000000 : ℝ)|=(5347386359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610238403/5000000000 : ℝ)|^4663 ≤ (21739269650119/50000000000000 : ℝ)^3639
        have hw : |(2610238403/5000000000 : ℝ)|=(2610238403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-936089657/5000000000 : ℝ)|^4663 ≤ (11683929613623/100000000000000 : ℝ)^3639
        have hw : |(-936089657/5000000000 : ℝ)|=(936089657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s5_3 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118907859/5000000000 : ℝ)*x 0 + (80017087/200000000 : ℝ)*x 1 + (897180351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118907859/5000000000 : ℝ)^4663 ≤ (33282913871583/100000000000000 : ℝ)^3639 := by
    have hnat : (2118907859 : ℕ)^4663*100000000000000^3639 ≤ 33282913871583^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118907859 5000000000 33282913871583 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80017087/200000000 : ℝ)^4663 ≤ (30917197403061/100000000000000 : ℝ)^3639 := by
    have hnat : (80017087 : ℕ)^4663*100000000000000^3639 ≤ 30917197403061^3639*200000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80017087 200000000 30917197403061 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897180351/2000000000 : ℝ)^4663 ≤ (223749304471/625000000000 : ℝ)^3639 := by
    have hnat : (897180351 : ℕ)^4663*625000000000^3639 ≤ 223749304471^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897180351 2000000000 223749304471 625000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118907859/5000000000 : ℝ), (80017087/200000000 : ℝ), (897180351/2000000000 : ℝ)] ![(33282913871583/100000000000000 : ℝ), (30917197403061/100000000000000 : ℝ), (223749304471/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118907859/5000000000 : ℝ)|^4663 ≤ (33282913871583/100000000000000 : ℝ)^3639
        have hw : |(2118907859/5000000000 : ℝ)|=(2118907859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80017087/200000000 : ℝ)|^4663 ≤ (30917197403061/100000000000000 : ℝ)^3639
        have hw : |(80017087/200000000 : ℝ)|=(80017087/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897180351/2000000000 : ℝ)|^4663 ≤ (223749304471/625000000000 : ℝ)^3639
        have hw : |(897180351/2000000000 : ℝ)|=(897180351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s5_4 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22100403/125000000 : ℝ)*x 0 + (5221540847/10000000000 : ℝ)*x 1 + (1084615941/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22100403/125000000 : ℝ)^4663 ≤ (5428838725281/50000000000000 : ℝ)^3639 := by
    have hnat : (22100403 : ℕ)^4663*50000000000000^3639 ≤ 5428838725281^3639*125000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22100403 125000000 5428838725281 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221540847/10000000000 : ℝ)^4663 ≤ (43489895132023/100000000000000 : ℝ)^3639 := by
    have hnat : (5221540847 : ℕ)^4663*100000000000000^3639 ≤ 43489895132023^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221540847 10000000000 43489895132023 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084615941/2000000000 : ℝ)^4663 ≤ (4565242740783/10000000000000 : ℝ)^3639 := by
    have hnat : (1084615941 : ℕ)^4663*10000000000000^3639 ≤ 4565242740783^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084615941 2000000000 4565242740783 10000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22100403/125000000 : ℝ), (5221540847/10000000000 : ℝ), (1084615941/2000000000 : ℝ)] ![(5428838725281/50000000000000 : ℝ), (43489895132023/100000000000000 : ℝ), (4565242740783/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22100403/125000000 : ℝ)|^4663 ≤ (5428838725281/50000000000000 : ℝ)^3639
        have hw : |(-22100403/125000000 : ℝ)|=(22100403/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221540847/10000000000 : ℝ)|^4663 ≤ (43489895132023/100000000000000 : ℝ)^3639
        have hw : |(5221540847/10000000000 : ℝ)|=(5221540847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084615941/2000000000 : ℝ)|^4663 ≤ (4565242740783/10000000000000 : ℝ)^3639
        have hw : |(1084615941/2000000000 : ℝ)|=(1084615941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s5_5 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646709951/5000000000 : ℝ)*x 0 + (-1669576419/10000000000 : ℝ)*x 1 + (216923159/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646709951/5000000000 : ℝ)^4663 ≤ (44258517446251/100000000000000 : ℝ)^3639 := by
    have hnat : (2646709951 : ℕ)^4663*100000000000000^3639 ≤ 44258517446251^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646709951 5000000000 44258517446251 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1669576419/10000000000 : ℝ)^4663 ≤ (5044531507033/50000000000000 : ℝ)^3639 := by
    have hnat : (1669576419 : ℕ)^4663*50000000000000^3639 ≤ 5044531507033^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669576419 10000000000 5044531507033 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216923159/400000000 : ℝ)^4663 ≤ (4565241953331/10000000000000 : ℝ)^3639 := by
    have hnat : (216923159 : ℕ)^4663*10000000000000^3639 ≤ 4565241953331^3639*400000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216923159 400000000 4565241953331 10000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646709951/5000000000 : ℝ), (-1669576419/10000000000 : ℝ), (216923159/400000000 : ℝ)] ![(44258517446251/100000000000000 : ℝ), (5044531507033/50000000000000 : ℝ), (4565241953331/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646709951/5000000000 : ℝ)|^4663 ≤ (44258517446251/100000000000000 : ℝ)^3639
        have hw : |(2646709951/5000000000 : ℝ)|=(2646709951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1669576419/10000000000 : ℝ)|^4663 ≤ (5044531507033/50000000000000 : ℝ)^3639
        have hw : |(-1669576419/10000000000 : ℝ)|=(1669576419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216923159/400000000 : ℝ)|^4663 ≤ (4565241953331/10000000000000 : ℝ)^3639
        have hw : |(216923159/400000000 : ℝ)|=(216923159/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s5_6 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058683873/2000000000 : ℝ)*x 0 + (1084615903/2000000000 : ℝ)*x 1 + (-1669576409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058683873/2000000000 : ℝ)^4663 ≤ (5532313961617/12500000000000 : ℝ)^3639 := by
    have hnat : (1058683873 : ℕ)^4663*12500000000000^3639 ≤ 5532313961617^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058683873 2000000000 5532313961617 12500000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084615903/2000000000 : ℝ)^4663 ≤ (22826212679149/50000000000000 : ℝ)^3639 := by
    have hnat : (1084615903 : ℕ)^4663*50000000000000^3639 ≤ 22826212679149^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084615903 2000000000 22826212679149 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1669576409/10000000000 : ℝ)^4663 ≤ (1261132867079/12500000000000 : ℝ)^3639 := by
    have hnat : (1669576409 : ℕ)^4663*12500000000000^3639 ≤ 1261132867079^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669576409 10000000000 1261132867079 12500000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058683873/2000000000 : ℝ), (1084615903/2000000000 : ℝ), (-1669576409/10000000000 : ℝ)] ![(5532313961617/12500000000000 : ℝ), (22826212679149/50000000000000 : ℝ), (1261132867079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058683873/2000000000 : ℝ)|^4663 ≤ (5532313961617/12500000000000 : ℝ)^3639
        have hw : |(1058683873/2000000000 : ℝ)|=(1058683873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084615903/2000000000 : ℝ)|^4663 ≤ (22826212679149/50000000000000 : ℝ)^3639
        have hw : |(1084615903/2000000000 : ℝ)|=(1084615903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1669576409/10000000000 : ℝ)|^4663 ≤ (1261132867079/12500000000000 : ℝ)^3639
        have hw : |(-1669576409/10000000000 : ℝ)|=(1669576409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s5_7 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4237877693/10000000000 : ℝ)*x 0 + (4483368917/10000000000 : ℝ)*x 1 + (80068133/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237877693/10000000000 : ℝ)^4663 ≤ (6656707515557/20000000000000 : ℝ)^3639 := by
    have hnat : (4237877693 : ℕ)^4663*20000000000000^3639 ≤ 6656707515557^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237877693 10000000000 6656707515557 20000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483368917/10000000000 : ℝ)^4663 ≤ (4471748675737/12500000000000 : ℝ)^3639 := by
    have hnat : (4483368917 : ℕ)^4663*12500000000000^3639 ≤ 4471748675737^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483368917 10000000000 4471748675737 12500000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80068133/200000000 : ℝ)^4663 ≤ (15471236500287/50000000000000 : ℝ)^3639 := by
    have hnat : (80068133 : ℕ)^4663*50000000000000^3639 ≤ 15471236500287^3639*200000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80068133 200000000 15471236500287 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237877693/10000000000 : ℝ), (4483368917/10000000000 : ℝ), (80068133/200000000 : ℝ)] ![(6656707515557/20000000000000 : ℝ), (4471748675737/12500000000000 : ℝ), (15471236500287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237877693/10000000000 : ℝ)|^4663 ≤ (6656707515557/20000000000000 : ℝ)^3639
        have hw : |(4237877693/10000000000 : ℝ)|=(4237877693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483368917/10000000000 : ℝ)|^4663 ≤ (4471748675737/12500000000000 : ℝ)^3639
        have hw : |(4483368917/10000000000 : ℝ)|=(4483368917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80068133/200000000 : ℝ)|^4663 ≤ (15471236500287/50000000000000 : ℝ)^3639
        have hw : |(80068133/200000000 : ℝ)|=(80068133/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1583_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11163/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (279/2500 : ℝ) ^ (4661/1024 : ℝ) ≤ (578239919822129/12500000000000000000 : ℝ) := by
    have hpowers : (279/2500 : ℝ)^4661 ≤ (578239919822129/12500000000000000000 : ℝ)^1024 := by
      have hnat : (279 : ℕ)^4661*12500000000000000000^1024 ≤ 578239919822129^1024*2500^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        279 2500 578239919822129 12500000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (279/2500 : ℝ)) (X := (578239919822129/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7743/50000 : ℝ) ^ (4661/1024 : ℝ) ≤ (20549425036279157/100000000000000000000 : ℝ) := by
    have hpowers : (7743/50000 : ℝ)^4661 ≤ (20549425036279157/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7743 : ℕ)^4661*100000000000000000000^1024 ≤ 20549425036279157^1024*50000^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7743 50000 20549425036279157 100000000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7743/50000 : ℝ)) (X := (20549425036279157/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250578239919822129/6250000000000000000 : ℝ) ≤ (1250025406406601/1250000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (6250578239919822129/6250000000000000000 : ℝ)^1024 ≤ (1250025406406601/1250000000000000 : ℝ)^4661 := by
      have hnat : (6250578239919822129 : ℕ)^1024*1250000000000000^4661 ≤ 1250025406406601^4661*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250578239919822129 6250000000000000000 1250025406406601 1250000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250025406406601/1250000000000000 : ℝ)) (X := (6250578239919822129/6250000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025175344394856189/100000000000000000000 : ℝ) ≤ (2500138259069483/2500000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (100025175344394856189/100000000000000000000 : ℝ)^1024 ≤ (2500138259069483/2500000000000000 : ℝ)^4661 := by
      have hnat : (100025175344394856189 : ℕ)^1024*2500000000000000^4661 ≤ 2500138259069483^4661*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025175344394856189 100000000000000000000 2500138259069483 2500000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500138259069483/2500000000000000 : ℝ)) (X := (100025175344394856189/100000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020549425036279157/50000000000000000000 : ℝ) ≤ (625056426331441/625000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (50020549425036279157/50000000000000000000 : ℝ)^1024 ≤ (625056426331441/625000000000000 : ℝ)^4661 := by
      have hnat : (50020549425036279157 : ℕ)^1024*625000000000000^4661 ≤ 625056426331441^4661*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020549425036279157 50000000000000000000 625056426331441 625000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625056426331441/625000000000000 : ℝ)) (X := (50020549425036279157/50000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(578239919822129/12500000000000000000 : ℝ) ≤ ((901105667982476661/901250000000000000 : ℝ)+2*(87446256281/108150000000000 : ℝ)*(279/2500 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (901105667982476661/901250000000000000 : ℝ)+2*(87446256281/108150000000000 : ℝ)*(279/2500 : ℝ)=(1250025406406601/1250000000000000 : ℝ) by norm_num, show 1+2*(578239919822129/12500000000000000000 : ℝ)=(6250578239919822129/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20549425036279157/100000000000000000000 : ℝ)+(578239919822129/12500000000000000000 : ℝ) ≤ ((901105667982476661/901250000000000000 : ℝ)+(87446256281/108150000000000 : ℝ)*((7743/50000 : ℝ)+(279/2500 : ℝ)))^(4661/1024 : ℝ) := by
    rw [show (901105667982476661/901250000000000000 : ℝ)+(87446256281/108150000000000 : ℝ)*((7743/50000 : ℝ)+(279/2500 : ℝ))=(2500138259069483/2500000000000000 : ℝ) by norm_num, show 1+(20549425036279157/100000000000000000000 : ℝ)+(578239919822129/12500000000000000000 : ℝ)=(100025175344394856189/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20549425036279157/100000000000000000000 : ℝ) ≤ ((901105667982476661/901250000000000000 : ℝ)+2*(87446256281/108150000000000 : ℝ)*(7743/50000 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (901105667982476661/901250000000000000 : ℝ)+2*(87446256281/108150000000000 : ℝ)*(7743/50000 : ℝ)=(625056426331441/625000000000000 : ℝ) by norm_num, show 1+2*(20549425036279157/100000000000000000000 : ℝ)=(50020549425036279157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (901105667982476661/901250000000000000 : ℝ)*(X 1 0+X 2 0)+(87446256281/108150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (901105667982476661/901250000000000000 : ℝ)) (alpha := (87446256281/108150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (901105667982476661/901250000000000000 : ℝ)*(X 0 1+X 2 1)+(87446256281/108150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (901105667982476661/901250000000000000 : ℝ)) (alpha := (87446256281/108150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (901105667982476661/901250000000000000 : ℝ)*(X 0 2+X 1 2)+(87446256281/108150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (901105667982476661/901250000000000000 : ℝ)) (alpha := (87446256281/108150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-884003143/5000000000 : ℝ)*X 0 0+(2712075679/5000000000 : ℝ)*X 0 1+(1305119197/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347386389/10000000000 : ℝ)*X 1 0+(-468044827/2500000000 : ℝ)*X 1 1+(261023839/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347386359/10000000000 : ℝ)*X 2 0+(2610238403/5000000000 : ℝ)*X 2 1+(-936089657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2118907859/5000000000 : ℝ)*X 0 0+(80017087/200000000 : ℝ)*X 0 1+(897180351/2000000000 : ℝ)*X 0 2+(2118907859/5000000000 : ℝ)*X 1 0+(80017087/200000000 : ℝ)*X 1 1+(897180351/2000000000 : ℝ)*X 1 2+(2118907859/5000000000 : ℝ)*X 2 0+(80017087/200000000 : ℝ)*X 2 1+(897180351/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-22100403/125000000 : ℝ)*X 0 0+(5221540847/10000000000 : ℝ)*X 0 1+(1084615941/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646709951/5000000000 : ℝ)*X 1 0+(-1669576419/10000000000 : ℝ)*X 1 1+(216923159/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058683873/2000000000 : ℝ)*X 2 0+(1084615903/2000000000 : ℝ)*X 2 1+(-1669576409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4237877693/10000000000 : ℝ)*X 0 0+(4483368917/10000000000 : ℝ)*X 0 1+(80068133/200000000 : ℝ)*X 0 2+(4237877693/10000000000 : ℝ)*X 1 0+(4483368917/10000000000 : ℝ)*X 1 1+(80068133/200000000 : ℝ)*X 1 2+(4237877693/10000000000 : ℝ)*X 2 0+(4483368917/10000000000 : ℝ)*X 2 1+(80068133/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50247267414927627143431519/22531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (192141737/50000000000000 : ℝ)*(base19) + (73221291/25000000000000 : ℝ)*(base23) + (34144797/100000000000000 : ℝ)*(lower2) + (80544227/100000000000000 : ℝ)*(upper3) + (24736587/100000000000000 : ℝ)*(upper5) + (3485731887595457/100000000000000 : ℝ)*(major0) + (3485731887595457/100000000000000 : ℝ)*(major1) + (3485731887595457/100000000000000 : ℝ)*(major2) + (2454899587249079/50000000000000 : ℝ)*(sp0) + (981960737269777/20000000000000 : ℝ)*(sp1) + (2454901888873597/50000000000000 : ℝ)*(sp2) + (515414127476199/25000000000000 : ℝ)*(sp3) + (4896134201/100000000000000 : ℝ)*(sp4) + (15601583/500000000000 : ℝ)*(sp7) + (515414907555349/25000000000000 : ℝ)*(f.failure) + (4909804070632359/100000000000000 : ℝ)*(f.sum) + (11875404011167/5407500000000000000000000000 : ℝ)*base65 + (1652520293797687231/270375000000000000000000000000000 : ℝ)*base67 + (2992779286770937231/270375000000000000000000000000000 : ℝ)*base69 + (2127428037914437231/270375000000000000000000000000000 : ℝ)*base71 + (8671945921733/5407500000000000000000000000 : ℝ)*base74 + (612439651458187769/270375000000000000000000000000000 : ℝ)*base76 + (4779320009901562231/270375000000000000000000000000000 : ℝ)*base77 + (4461939453655312231/270375000000000000000000000000000 : ℝ)*base79 + (27277254545663/5407500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (523609/312500000000000000000 : ℝ)*base90 + (523609/312500000000000000000 : ℝ)*base92 + (523609/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35775033118724858891085147/3218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (977627109/50000000000000 : ℝ)*(base19) + (869759147/50000000000000 : ℝ)*(base23) + (202608871/50000000000000 : ℝ)*(lower1) + (63737883/50000000000000 : ℝ)*(upper3) + (24261321/20000000000000 : ℝ)*(lower4) + (3522641981124987/100000000000000 : ℝ)*(major0) + (3522641981124987/100000000000000 : ℝ)*(major1) + (3522641981124987/100000000000000 : ℝ)*(major2) + (5733785031/100000000000000 : ℝ)*(sp2) + (1039593931/100000000000000 : ℝ)*(sp3) + (992358647565851/20000000000000 : ℝ)*(sp4) + (4961791282575037/100000000000000 : ℝ)*(sp5) + (4961785764525929/100000000000000 : ℝ)*(sp6) + (16277260268289/781250000000 : ℝ)*(sp7) + (2083490353934923/100000000000000 : ℝ)*(f.failure) + (992358647565851/20000000000000 : ℝ)*(f.sum) + (200741449463/64375000000000000000000000 : ℝ)*base65 + (129824719448611201/12875000000000000000000000000000 : ℝ)*base67 + (217204241818236201/12875000000000000000000000000000 : ℝ)*base69 + (174314143040236201/12875000000000000000000000000000 : ℝ)*base71 + (406237932251/515000000000000000000000000 : ℝ)*base74 + (269106234080736201/12875000000000000000000000000000 : ℝ)*base75 + (352545074725236201/12875000000000000000000000000000 : ℝ)*base77 + (431237607164888799/12875000000000000000000000000000 : ℝ)*base80 + (78143412921/32187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5672943/1250000000000000000000 : ℝ)*base90 + (5672943/1250000000000000000000 : ℝ)*base92 + (5672943/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1583_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1583_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1583_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1583_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1583_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1583_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1583_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

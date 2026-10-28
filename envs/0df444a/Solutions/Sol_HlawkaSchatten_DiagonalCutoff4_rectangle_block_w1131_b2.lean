-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1131_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:52.673879+00:00
-- url     : https://prove2.me/submissions/b6ce0020-4d0d-4639-95d1-760af32c1f3b

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
theorem support_rectangle_w1131_s6_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086063111/5000000000 : ℝ)*x 0 + (5393599289/10000000000 : ℝ)*x 1 + (5265213317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086063111/5000000000 : ℝ)^2081 ≤ (6598811739143/50000000000000 : ℝ)^1569 := by
    have hnat : (1086063111 : ℕ)^2081*50000000000000^1569 ≤ 6598811739143^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086063111 5000000000 6598811739143 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393599289/10000000000 : ℝ)^2081 ≤ (44094523946463/100000000000000 : ℝ)^1569 := by
    have hnat : (5393599289 : ℕ)^2081*100000000000000^1569 ≤ 44094523946463^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393599289 10000000000 44094523946463 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265213317/10000000000 : ℝ)^2081 ≤ (10676963139507/25000000000000 : ℝ)^1569 := by
    have hnat : (5265213317 : ℕ)^2081*25000000000000^1569 ≤ 10676963139507^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265213317 10000000000 10676963139507 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086063111/5000000000 : ℝ), (5393599289/10000000000 : ℝ), (5265213317/10000000000 : ℝ)] ![(6598811739143/50000000000000 : ℝ), (44094523946463/100000000000000 : ℝ), (10676963139507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086063111/5000000000 : ℝ)|^2081 ≤ (6598811739143/50000000000000 : ℝ)^1569
        have hw : |(-1086063111/5000000000 : ℝ)|=(1086063111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393599289/10000000000 : ℝ)|^2081 ≤ (44094523946463/100000000000000 : ℝ)^1569
        have hw : |(5393599289/10000000000 : ℝ)|=(5393599289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265213317/10000000000 : ℝ)|^2081 ≤ (10676963139507/25000000000000 : ℝ)^1569
        have hw : |(5265213317/10000000000 : ℝ)|=(5265213317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s6_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336222367/2500000000 : ℝ)*x 0 + (-1118626891/5000000000 : ℝ)*x 1 + (5265213311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336222367/2500000000 : ℝ)^2081 ≤ (43567136322591/100000000000000 : ℝ)^1569 := by
    have hnat : (1336222367 : ℕ)^2081*100000000000000^1569 ≤ 43567136322591^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336222367 2500000000 43567136322591 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118626891/5000000000 : ℝ)^2081 ≤ (13725011180969/100000000000000 : ℝ)^1569 := by
    have hnat : (1118626891 : ℕ)^2081*100000000000000^1569 ≤ 13725011180969^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118626891 5000000000 13725011180969 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265213311/10000000000 : ℝ)^2081 ≤ (42707852493479/100000000000000 : ℝ)^1569 := by
    have hnat : (5265213311 : ℕ)^2081*100000000000000^1569 ≤ 42707852493479^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265213311 10000000000 42707852493479 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336222367/2500000000 : ℝ), (-1118626891/5000000000 : ℝ), (5265213311/10000000000 : ℝ)] ![(43567136322591/100000000000000 : ℝ), (13725011180969/100000000000000 : ℝ), (42707852493479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336222367/2500000000 : ℝ)|^2081 ≤ (43567136322591/100000000000000 : ℝ)^1569
        have hw : |(1336222367/2500000000 : ℝ)|=(1336222367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118626891/5000000000 : ℝ)|^2081 ≤ (13725011180969/100000000000000 : ℝ)^1569
        have hw : |(-1118626891/5000000000 : ℝ)|=(1118626891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265213311/10000000000 : ℝ)|^2081 ≤ (42707852493479/100000000000000 : ℝ)^1569
        have hw : |(5265213311/10000000000 : ℝ)|=(5265213311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s6_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068977891/2000000000 : ℝ)*x 0 + (5265213319/10000000000 : ℝ)*x 1 + (-559313447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068977891/2000000000 : ℝ)^2081 ≤ (43567136182047/100000000000000 : ℝ)^1569 := by
    have hnat : (1068977891 : ℕ)^2081*100000000000000^1569 ≤ 43567136182047^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068977891 2000000000 43567136182047 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265213319/10000000000 : ℝ)^2081 ≤ (8541570515909/20000000000000 : ℝ)^1569 := by
    have hnat : (5265213319 : ℕ)^2081*20000000000000^1569 ≤ 8541570515909^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265213319 10000000000 8541570515909 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559313447/2500000000 : ℝ)^2081 ≤ (13725011229789/100000000000000 : ℝ)^1569 := by
    have hnat : (559313447 : ℕ)^2081*100000000000000^1569 ≤ 13725011229789^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559313447 2500000000 13725011229789 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068977891/2000000000 : ℝ), (5265213319/10000000000 : ℝ), (-559313447/2500000000 : ℝ)] ![(43567136182047/100000000000000 : ℝ), (8541570515909/20000000000000 : ℝ), (13725011229789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068977891/2000000000 : ℝ)|^2081 ≤ (43567136182047/100000000000000 : ℝ)^1569
        have hw : |(1068977891/2000000000 : ℝ)|=(1068977891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265213319/10000000000 : ℝ)|^2081 ≤ (8541570515909/20000000000000 : ℝ)^1569
        have hw : |(5265213319/10000000000 : ℝ)|=(5265213319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-559313447/2500000000 : ℝ)|^2081 ≤ (13725011229789/100000000000000 : ℝ)^1569
        have hw : |(-559313447/2500000000 : ℝ)|=(559313447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s6_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4366206873/10000000000 : ℝ)*x 0 + (1060156849/2500000000 : ℝ)*x 1 + (4495497017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366206873/10000000000 : ℝ)^2081 ≤ (33316720684291/100000000000000 : ℝ)^1569 := by
    have hnat : (4366206873 : ℕ)^2081*100000000000000^1569 ≤ 33316720684291^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366206873 10000000000 33316720684291 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060156849/2500000000 : ℝ)^2081 ≤ (32051781903899/100000000000000 : ℝ)^1569 := by
    have hnat : (1060156849 : ℕ)^2081*100000000000000^1569 ≤ 32051781903899^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060156849 2500000000 32051781903899 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495497017/10000000000 : ℝ)^2081 ≤ (34631497390021/100000000000000 : ℝ)^1569 := by
    have hnat : (4495497017 : ℕ)^2081*100000000000000^1569 ≤ 34631497390021^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495497017 10000000000 34631497390021 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366206873/10000000000 : ℝ), (1060156849/2500000000 : ℝ), (4495497017/10000000000 : ℝ)] ![(33316720684291/100000000000000 : ℝ), (32051781903899/100000000000000 : ℝ), (34631497390021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366206873/10000000000 : ℝ)|^2081 ≤ (33316720684291/100000000000000 : ℝ)^1569
        have hw : |(4366206873/10000000000 : ℝ)|=(4366206873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060156849/2500000000 : ℝ)|^2081 ≤ (32051781903899/100000000000000 : ℝ)^1569
        have hw : |(1060156849/2500000000 : ℝ)|=(1060156849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495497017/10000000000 : ℝ)|^2081 ≤ (34631497390021/100000000000000 : ℝ)^1569
        have hw : |(4495497017/10000000000 : ℝ)|=(4495497017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s6_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172131217/10000000000 : ℝ)*x 0 + (2632768777/5000000000 : ℝ)*x 1 + (337079617/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172131217/10000000000 : ℝ)^2081 ≤ (3299415932757/25000000000000 : ℝ)^1569 := by
    have hnat : (2172131217 : ℕ)^2081*25000000000000^1569 ≤ 3299415932757^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172131217 10000000000 3299415932757 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632768777/5000000000 : ℝ)^2081 ≤ (42711340809903/100000000000000 : ℝ)^1569 := by
    have hnat : (2632768777 : ℕ)^2081*100000000000000^1569 ≤ 42711340809903^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632768777 5000000000 42711340809903 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337079617/625000000 : ℝ)^2081 ≤ (44090995438689/100000000000000 : ℝ)^1569 := by
    have hnat : (337079617 : ℕ)^2081*100000000000000^1569 ≤ 44090995438689^1569*625000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337079617 625000000 44090995438689 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172131217/10000000000 : ℝ), (2632768777/5000000000 : ℝ), (337079617/625000000 : ℝ)] ![(3299415932757/25000000000000 : ℝ), (42711340809903/100000000000000 : ℝ), (44090995438689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172131217/10000000000 : ℝ)|^2081 ≤ (3299415932757/25000000000000 : ℝ)^1569
        have hw : |(-2172131217/10000000000 : ℝ)|=(2172131217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632768777/5000000000 : ℝ)|^2081 ≤ (42711340809903/100000000000000 : ℝ)^1569
        have hw : |(2632768777/5000000000 : ℝ)|=(2632768777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337079617/625000000 : ℝ)|^2081 ≤ (44090995438689/100000000000000 : ℝ)^1569
        have hw : |(337079617/625000000 : ℝ)|=(337079617/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s6_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312388979/10000000000 : ℝ)*x 0 + (-65912289/312500000 : ℝ)*x 1 + (5393273873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312388979/10000000000 : ℝ)^2081 ≤ (21608059868413/50000000000000 : ℝ)^1569 := by
    have hnat : (5312388979 : ℕ)^2081*50000000000000^1569 ≤ 21608059868413^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312388979 10000000000 21608059868413 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65912289/312500000 : ℝ)^2081 ≤ (1586610599853/12500000000000 : ℝ)^1569 := by
    have hnat : (65912289 : ℕ)^2081*12500000000000^1569 ≤ 1586610599853^1569*312500000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65912289 312500000 1586610599853 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393273873/10000000000 : ℝ)^2081 ≤ (11022748862383/25000000000000 : ℝ)^1569 := by
    have hnat : (5393273873 : ℕ)^2081*25000000000000^1569 ≤ 11022748862383^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393273873 10000000000 11022748862383 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312388979/10000000000 : ℝ), (-65912289/312500000 : ℝ), (5393273873/10000000000 : ℝ)] ![(21608059868413/50000000000000 : ℝ), (1586610599853/12500000000000 : ℝ), (11022748862383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312388979/10000000000 : ℝ)|^2081 ≤ (21608059868413/50000000000000 : ℝ)^1569
        have hw : |(5312388979/10000000000 : ℝ)|=(5312388979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65912289/312500000 : ℝ)|^2081 ≤ (1586610599853/12500000000000 : ℝ)^1569
        have hw : |(-65912289/312500000 : ℝ)|=(65912289/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393273873/10000000000 : ℝ)|^2081 ≤ (11022748862383/25000000000000 : ℝ)^1569
        have hw : |(5393273873/10000000000 : ℝ)|=(5393273873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s6_6 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312388977/10000000000 : ℝ)*x 0 + (1348318471/2500000000 : ℝ)*x 1 + (-527298309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312388977/10000000000 : ℝ)^2081 ≤ (43216119715247/100000000000000 : ℝ)^1569 := by
    have hnat : (5312388977 : ℕ)^2081*100000000000000^1569 ≤ 43216119715247^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312388977 10000000000 43216119715247 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348318471/2500000000 : ℝ)^2081 ≤ (11022748892201/25000000000000 : ℝ)^1569 := by
    have hnat : (1348318471 : ℕ)^2081*25000000000000^1569 ≤ 11022748892201^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348318471 2500000000 11022748892201 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527298309/2500000000 : ℝ)^2081 ≤ (3173221175761/25000000000000 : ℝ)^1569 := by
    have hnat : (527298309 : ℕ)^2081*25000000000000^1569 ≤ 3173221175761^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527298309 2500000000 3173221175761 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312388977/10000000000 : ℝ), (1348318471/2500000000 : ℝ), (-527298309/2500000000 : ℝ)] ![(43216119715247/100000000000000 : ℝ), (11022748892201/25000000000000 : ℝ), (3173221175761/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312388977/10000000000 : ℝ)|^2081 ≤ (43216119715247/100000000000000 : ℝ)^1569
        have hw : |(5312388977/10000000000 : ℝ)|=(5312388977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348318471/2500000000 : ℝ)|^2081 ≤ (11022748892201/25000000000000 : ℝ)^1569
        have hw : |(1348318471/2500000000 : ℝ)|=(1348318471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527298309/2500000000 : ℝ)|^2081 ≤ (3173221175761/25000000000000 : ℝ)^1569
        have hw : |(-527298309/2500000000 : ℝ)|=(527298309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s6_7 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2183108393/5000000000 : ℝ)*x 0 + (2247426671/5000000000 : ℝ)*x 1 + (4241273409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183108393/5000000000 : ℝ)^2081 ≤ (1332672840401/4000000000000 : ℝ)^1569 := by
    have hnat : (2183108393 : ℕ)^2081*4000000000000^1569 ≤ 1332672840401^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183108393 5000000000 1332672840401 4000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247426671/5000000000 : ℝ)^2081 ≤ (34624920823943/100000000000000 : ℝ)^1569 := by
    have hnat : (2247426671 : ℕ)^2081*100000000000000^1569 ≤ 34624920823943^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247426671 5000000000 34624920823943 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241273409/10000000000 : ℝ)^2081 ≤ (200364113429/625000000000 : ℝ)^1569 := by
    have hnat : (4241273409 : ℕ)^2081*625000000000^1569 ≤ 200364113429^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241273409 10000000000 200364113429 625000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183108393/5000000000 : ℝ), (2247426671/5000000000 : ℝ), (4241273409/10000000000 : ℝ)] ![(1332672840401/4000000000000 : ℝ), (34624920823943/100000000000000 : ℝ), (200364113429/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183108393/5000000000 : ℝ)|^2081 ≤ (1332672840401/4000000000000 : ℝ)^1569
        have hw : |(2183108393/5000000000 : ℝ)|=(2183108393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247426671/5000000000 : ℝ)|^2081 ≤ (34624920823943/100000000000000 : ℝ)^1569
        have hw : |(2247426671/5000000000 : ℝ)|=(2247426671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241273409/10000000000 : ℝ)|^2081 ≤ (200364113429/625000000000 : ℝ)^1569
        have hw : |(4241273409/10000000000 : ℝ)|=(4241273409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11331/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11299/100000 : ℝ) ^ (8323/2048 : ℝ) ≤ (14177115798505757/100000000000000000000 : ℝ) := by
    have hpowers : (11299/100000 : ℝ)^8323 ≤ (14177115798505757/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11299 : ℕ)^8323*100000000000000000000^2048 ≤ 14177115798505757^2048*100000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11299 100000 14177115798505757 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11299/100000 : ℝ)) (X := (14177115798505757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3521/25000 : ℝ) ^ (8323/2048 : ℝ) ≤ (34709827732711851/100000000000000000000 : ℝ) := by
    have hpowers : (3521/25000 : ℝ)^8323 ≤ (34709827732711851/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3521 : ℕ)^8323*100000000000000000000^2048 ≤ 34709827732711851^2048*25000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3521 25000 34709827732711851 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3521/25000 : ℝ)) (X := (34709827732711851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014177115798505757/50000000000000000000 : ℝ) ≤ (10000697624180147/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50014177115798505757/50000000000000000000 : ℝ)^2048 ≤ (10000697624180147/10000000000000000 : ℝ)^8323 := by
      have hnat : (50014177115798505757 : ℕ)^2048*10000000000000000^8323 ≤ 10000697624180147^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014177115798505757 50000000000000000000 10000697624180147 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000697624180147/10000000000000000 : ℝ)) (X := (50014177115798505757/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506110867941402201/12500000000000000000 : ℝ) ≤ (2000240543108587/2000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (12506110867941402201/12500000000000000000 : ℝ)^2048 ≤ (2000240543108587/2000000000000000 : ℝ)^8323 := by
      have hnat : (12506110867941402201 : ℕ)^2048*2000000000000000^8323 ≤ 2000240543108587^8323*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506110867941402201 12500000000000000000 2000240543108587 2000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000240543108587/2000000000000000 : ℝ)) (X := (12506110867941402201/12500000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034709827732711851/50000000000000000000 : ℝ) ≤ (10001707806905723/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50034709827732711851/50000000000000000000 : ℝ)^2048 ≤ (10001707806905723/10000000000000000 : ℝ)^8323 := by
      have hnat : (50034709827732711851 : ℕ)^2048*10000000000000000^8323 ≤ 10001707806905723^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034709827732711851 50000000000000000000 10001707806905723 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001707806905723/10000000000000000 : ℝ)) (X := (50034709827732711851/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14177115798505757/100000000000000000000 : ℝ) ≤ ((27840528828725426171/27850000000000000000 : ℝ)+2*(126272840697/69625000000000 : ℝ)*(11299/100000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (27840528828725426171/27850000000000000000 : ℝ)+2*(126272840697/69625000000000 : ℝ)*(11299/100000 : ℝ)=(10000697624180147/10000000000000000 : ℝ) by norm_num, show 1+2*(14177115798505757/100000000000000000000 : ℝ)=(50014177115798505757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34709827732711851/100000000000000000000 : ℝ)+(14177115798505757/100000000000000000000 : ℝ) ≤ ((27840528828725426171/27850000000000000000 : ℝ)+(126272840697/69625000000000 : ℝ)*((3521/25000 : ℝ)+(11299/100000 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (27840528828725426171/27850000000000000000 : ℝ)+(126272840697/69625000000000 : ℝ)*((3521/25000 : ℝ)+(11299/100000 : ℝ))=(2000240543108587/2000000000000000 : ℝ) by norm_num, show 1+(34709827732711851/100000000000000000000 : ℝ)+(14177115798505757/100000000000000000000 : ℝ)=(12506110867941402201/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34709827732711851/100000000000000000000 : ℝ) ≤ ((27840528828725426171/27850000000000000000 : ℝ)+2*(126272840697/69625000000000 : ℝ)*(3521/25000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (27840528828725426171/27850000000000000000 : ℝ)+2*(126272840697/69625000000000 : ℝ)*(3521/25000 : ℝ)=(10001707806905723/10000000000000000 : ℝ) by norm_num, show 1+2*(34709827732711851/100000000000000000000 : ℝ)=(50034709827732711851/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27840528828725426171/27850000000000000000 : ℝ)*(X 1 0+X 2 0)+(126272840697/69625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (27840528828725426171/27850000000000000000 : ℝ)) (alpha := (126272840697/69625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27840528828725426171/27850000000000000000 : ℝ)*(X 0 1+X 2 1)+(126272840697/69625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (27840528828725426171/27850000000000000000 : ℝ)) (alpha := (126272840697/69625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27840528828725426171/27850000000000000000 : ℝ)*(X 0 2+X 1 2)+(126272840697/69625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (27840528828725426171/27850000000000000000 : ℝ)) (alpha := (126272840697/69625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1086063111/5000000000 : ℝ)*X 0 0+(5393599289/10000000000 : ℝ)*X 0 1+(5265213317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336222367/2500000000 : ℝ)*X 1 0+(-1118626891/5000000000 : ℝ)*X 1 1+(5265213311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068977891/2000000000 : ℝ)*X 2 0+(5265213319/10000000000 : ℝ)*X 2 1+(-559313447/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366206873/10000000000 : ℝ)*X 0 0+(1060156849/2500000000 : ℝ)*X 0 1+(4495497017/10000000000 : ℝ)*X 0 2+(4366206873/10000000000 : ℝ)*X 1 0+(1060156849/2500000000 : ℝ)*X 1 1+(4495497017/10000000000 : ℝ)*X 1 2+(4366206873/10000000000 : ℝ)*X 2 0+(1060156849/2500000000 : ℝ)*X 2 1+(4495497017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2172131217/10000000000 : ℝ)*X 0 0+(2632768777/5000000000 : ℝ)*X 0 1+(337079617/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312388979/10000000000 : ℝ)*X 1 0+(-65912289/312500000 : ℝ)*X 1 1+(5393273873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312388977/10000000000 : ℝ)*X 2 0+(1348318471/2500000000 : ℝ)*X 2 1+(-527298309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183108393/5000000000 : ℝ)*X 0 0+(2247426671/5000000000 : ℝ)*X 0 1+(4241273409/10000000000 : ℝ)*X 0 2+(2183108393/5000000000 : ℝ)*X 1 0+(2247426671/5000000000 : ℝ)*X 1 1+(4241273409/10000000000 : ℝ)*X 1 2+(2183108393/5000000000 : ℝ)*X 2 0+(2247426671/5000000000 : ℝ)*X 2 1+(4241273409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5650331826705850018306728549/696250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1676476857/100000000000000 : ℝ)*(base19) + (307004641/20000000000000 : ℝ)*(base23) + (65479577/100000000000000 : ℝ)*(lower2) + (53444343/25000000000000 : ℝ)*(upper3) + (10941299/10000000000000 : ℝ)*(upper5) + (2928182080124409/50000000000000 : ℝ)*(major0) + (2928182080124409/50000000000000 : ℝ)*(major1) + (2928182080124409/50000000000000 : ℝ)*(major2) + (7789061057924999/100000000000000 : ℝ)*(sp0) + (7789104307475213/100000000000000 : ℝ)*(sp1) + (3894552224464433/50000000000000 : ℝ)*(sp2) + (980899247765143/25000000000000 : ℝ)*(sp3) + (701969173/1562500000000 : ℝ)*(sp4) + (5014994477/20000000000000 : ℝ)*(sp7) + (1961811033016479/50000000000000 : ℝ)*(f.failure) + (7789105983952071/100000000000000 : ℝ)*(f.sum) + (2352834761029/3481250000000000000000000000 : ℝ)*base66 + (17004453223911207939/1392500000000000000000000000000000 : ℝ)*base67 + (11697747297973707939/1392500000000000000000000000000000 : ℝ)*base69 + (37676890136328707939/1392500000000000000000000000000000 : ℝ)*base71 + (2210055497723/1740625000000000000000000000 : ℝ)*base73 + (32604901354893707939/1392500000000000000000000000000000 : ℝ)*base75 + (20557841387023707939/1392500000000000000000000000000000 : ℝ)*base77 + (5184385946823707939/1392500000000000000000000000000000 : ℝ)*base79 + (40289249765841/13925000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3120327/500000000000000000000 : ℝ)*base89 + (3120327/500000000000000000000 : ℝ)*base91 + (3120327/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6760830490461372828563154387/696250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1766510701/100000000000000 : ℝ)*(base19) + (121019409/6250000000000 : ℝ)*(base23) + (24491257/12500000000000 : ℝ)*(upper3) + (15176341/20000000000000 : ℝ)*(lower4) + (193904059/100000000000000 : ℝ)*(upper5) + (5886077233833299/100000000000000 : ℝ)*(major0) + (5886077233833299/100000000000000 : ℝ)*(major1) + (5886077233833299/100000000000000 : ℝ)*(major2) + (24154036823/50000000000000 : ℝ)*(sp1) + (53196726367/100000000000000 : ℝ)*(sp2) + (3914312519355623/50000000000000 : ℝ)*(sp4) + (7828574964126899/100000000000000 : ℝ)*(sp5) + (1565713981134867/20000000000000 : ℝ)*(sp6) + (985882276319261/25000000000000 : ℝ)*(sp7) + (985882276319261/25000000000000 : ℝ)*(f.failure) + (3914312519355623/50000000000000 : ℝ)*(f.sum) + (20380491057381/6962500000000000000000000000 : ℝ)*base65 + (22983671208112931871/2785000000000000000000000000000000 : ℝ)*base68 + (28329685288272931871/2785000000000000000000000000000000 : ℝ)*base70 + (6514899234602068129/2785000000000000000000000000000000 : ℝ)*base71 + (8860476939261/1740625000000000000000000000 : ℝ)*base74 + (41464712298757931871/2785000000000000000000000000000000 : ℝ)*base76 + (15836839109732931871/2785000000000000000000000000000000 : ℝ)*base78 + (49486613855377931871/2785000000000000000000000000000000 : ℝ)*base80 + (6284661471639/1740625000000000000000000000 : ℝ)*base81 + (2410293/250000000000000000000 : ℝ)*base89 + (2410293/250000000000000000000 : ℝ)*base91 + (2410293/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1131_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1131_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1131_s7_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172153629/10000000000 : ℝ)*x 0 + (5393265427/10000000000 : ℝ)*x 1 + (2632764639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172153629/10000000000 : ℝ)^2081 ≤ (13197844340899/100000000000000 : ℝ)^1569 := by
    have hnat : (2172153629 : ℕ)^2081*100000000000000^1569 ≤ 13197844340899^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172153629 10000000000 13197844340899 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393265427/10000000000 : ℝ)^2081 ≤ (44090903870187/100000000000000 : ℝ)^1569 := by
    have hnat : (5393265427 : ℕ)^2081*100000000000000^1569 ≤ 44090903870187^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393265427 10000000000 44090903870187 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632764639/5000000000 : ℝ)^2081 ≤ (4271125177301/10000000000000 : ℝ)^1569 := by
    have hnat : (2632764639 : ℕ)^2081*10000000000000^1569 ≤ 4271125177301^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632764639 5000000000 4271125177301 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172153629/10000000000 : ℝ), (5393265427/10000000000 : ℝ), (2632764639/5000000000 : ℝ)] ![(13197844340899/100000000000000 : ℝ), (44090903870187/100000000000000 : ℝ), (4271125177301/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172153629/10000000000 : ℝ)|^2081 ≤ (13197844340899/100000000000000 : ℝ)^1569
        have hw : |(-2172153629/10000000000 : ℝ)|=(2172153629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393265427/10000000000 : ℝ)|^2081 ≤ (44090903870187/100000000000000 : ℝ)^1569
        have hw : |(5393265427/10000000000 : ℝ)|=(5393265427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632764639/5000000000 : ℝ)|^2081 ≤ (4271125177301/10000000000000 : ℝ)^1569
        have hw : |(2632764639/5000000000 : ℝ)|=(2632764639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s7_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336201507/2500000000 : ℝ)*x 0 + (-2236946853/10000000000 : ℝ)*x 1 + (5265529289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336201507/2500000000 : ℝ)^2081 ≤ (2722889640479/6250000000000 : ℝ)^1569 := by
    have hnat : (1336201507 : ℕ)^2081*6250000000000^1569 ≤ 2722889640479^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336201507 2500000000 2722889640479 6250000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236946853/10000000000 : ℝ)^2081 ≤ (6861256928759/50000000000000 : ℝ)^1569 := by
    have hnat : (2236946853 : ℕ)^2081*50000000000000^1569 ≤ 6861256928759^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236946853 10000000000 6861256928759 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265529289/10000000000 : ℝ)^2081 ≤ (5338906486419/12500000000000 : ℝ)^1569 := by
    have hnat : (5265529289 : ℕ)^2081*12500000000000^1569 ≤ 5338906486419^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265529289 10000000000 5338906486419 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336201507/2500000000 : ℝ), (-2236946853/10000000000 : ℝ), (5265529289/10000000000 : ℝ)] ![(2722889640479/6250000000000 : ℝ), (6861256928759/50000000000000 : ℝ), (5338906486419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336201507/2500000000 : ℝ)|^2081 ≤ (2722889640479/6250000000000 : ℝ)^1569
        have hw : |(1336201507/2500000000 : ℝ)|=(1336201507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2236946853/10000000000 : ℝ)|^2081 ≤ (6861256928759/50000000000000 : ℝ)^1569
        have hw : |(-2236946853/10000000000 : ℝ)|=(2236946853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265529289/10000000000 : ℝ)|^2081 ≤ (5338906486419/12500000000000 : ℝ)^1569
        have hw : |(5265529289/10000000000 : ℝ)|=(5265529289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s7_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (334050377/625000000 : ℝ)*x 0 + (5265529291/10000000000 : ℝ)*x 1 + (-559236711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334050377/625000000 : ℝ)^2081 ≤ (10891558572727/25000000000000 : ℝ)^1569 := by
    have hnat : (334050377 : ℕ)^2081*25000000000000^1569 ≤ 10891558572727^1569*625000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334050377 625000000 10891558572727 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265529291/10000000000 : ℝ)^2081 ≤ (42711251912869/100000000000000 : ℝ)^1569 := by
    have hnat : (5265529291 : ℕ)^2081*100000000000000^1569 ≤ 42711251912869^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265529291 10000000000 42711251912869 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559236711/2500000000 : ℝ)^2081 ≤ (3430628446073/25000000000000 : ℝ)^1569 := by
    have hnat : (559236711 : ℕ)^2081*25000000000000^1569 ≤ 3430628446073^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559236711 2500000000 3430628446073 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334050377/625000000 : ℝ), (5265529291/10000000000 : ℝ), (-559236711/2500000000 : ℝ)] ![(10891558572727/25000000000000 : ℝ), (42711251912869/100000000000000 : ℝ), (3430628446073/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334050377/625000000 : ℝ)|^2081 ≤ (10891558572727/25000000000000 : ℝ)^1569
        have hw : |(334050377/625000000 : ℝ)|=(334050377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265529291/10000000000 : ℝ)|^2081 ≤ (42711251912869/100000000000000 : ℝ)^1569
        have hw : |(5265529291/10000000000 : ℝ)|=(5265529291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-559236711/2500000000 : ℝ)|^2081 ≤ (3430628446073/25000000000000 : ℝ)^1569
        have hw : |(-559236711/2500000000 : ℝ)|=(559236711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s7_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2183111719/5000000000 : ℝ)*x 0 + (530158787/1250000000 : ℝ)*x 1 + (4494849807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183111719/5000000000 : ℝ)^2081 ≤ (33316888332449/100000000000000 : ℝ)^1569 := by
    have hnat : (2183111719 : ℕ)^2081*100000000000000^1569 ≤ 33316888332449^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183111719 5000000000 33316888332449 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530158787/1250000000 : ℝ)^2081 ≤ (6411645388043/20000000000000 : ℝ)^1569 := by
    have hnat : (530158787 : ℕ)^2081*20000000000000^1569 ≤ 6411645388043^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530158787 1250000000 6411645388043 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494849807/10000000000 : ℝ)^2081 ≤ (6924976941387/20000000000000 : ℝ)^1569 := by
    have hnat : (4494849807 : ℕ)^2081*20000000000000^1569 ≤ 6924976941387^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494849807 10000000000 6924976941387 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183111719/5000000000 : ℝ), (530158787/1250000000 : ℝ), (4494849807/10000000000 : ℝ)] ![(33316888332449/100000000000000 : ℝ), (6411645388043/20000000000000 : ℝ), (6924976941387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183111719/5000000000 : ℝ)|^2081 ≤ (33316888332449/100000000000000 : ℝ)^1569
        have hw : |(2183111719/5000000000 : ℝ)|=(2183111719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530158787/1250000000 : ℝ)|^2081 ≤ (6411645388043/20000000000000 : ℝ)^1569
        have hw : |(530158787/1250000000 : ℝ)|=(530158787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494849807/10000000000 : ℝ)|^2081 ≤ (6924976941387/20000000000000 : ℝ)^1569
        have hw : |(4494849807/10000000000 : ℝ)|=(4494849807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s7_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172158489/10000000000 : ℝ)*x 0 + (658231327/1250000000 : ℝ)*x 1 + (2696471487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172158489/10000000000 : ℝ)^2081 ≤ (1319788350589/10000000000000 : ℝ)^1569 := by
    have hnat : (2172158489 : ℕ)^2081*10000000000000^1569 ≤ 1319788350589^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172158489 10000000000 1319788350589 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658231327/1250000000 : ℝ)^2081 ≤ (266966930649/625000000000 : ℝ)^1569 := by
    have hnat : (658231327 : ℕ)^2081*625000000000^1569 ≤ 266966930649^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658231327 1250000000 266966930649 625000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696471487/5000000000 : ℝ)^2081 ≤ (22043703785741/50000000000000 : ℝ)^1569 := by
    have hnat : (2696471487 : ℕ)^2081*50000000000000^1569 ≤ 22043703785741^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696471487 5000000000 22043703785741 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172158489/10000000000 : ℝ), (658231327/1250000000 : ℝ), (2696471487/5000000000 : ℝ)] ![(1319788350589/10000000000000 : ℝ), (266966930649/625000000000 : ℝ), (22043703785741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172158489/10000000000 : ℝ)|^2081 ≤ (1319788350589/10000000000000 : ℝ)^1569
        have hw : |(-2172158489/10000000000 : ℝ)|=(2172158489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658231327/1250000000 : ℝ)|^2081 ≤ (266966930649/625000000000 : ℝ)^1569
        have hw : |(658231327/1250000000 : ℝ)|=(658231327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696471487/5000000000 : ℝ)|^2081 ≤ (22043703785741/50000000000000 : ℝ)^1569
        have hw : |(2696471487/5000000000 : ℝ)|=(2696471487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s7_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328117319/2500000000 : ℝ)*x 0 + (-2109533059/10000000000 : ℝ)*x 1 + (269647191/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328117319/2500000000 : ℝ)^2081 ≤ (21608493055433/50000000000000 : ℝ)^1569 := by
    have hnat : (1328117319 : ℕ)^2081*50000000000000^1569 ≤ 21608493055433^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328117319 2500000000 21608493055433 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109533059/10000000000 : ℝ)^2081 ≤ (12695597125227/100000000000000 : ℝ)^1569 := by
    have hnat : (2109533059 : ℕ)^2081*100000000000000^1569 ≤ 12695597125227^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109533059 10000000000 12695597125227 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269647191/500000000 : ℝ)^2081 ≤ (8817483348883/20000000000000 : ℝ)^1569 := by
    have hnat : (269647191 : ℕ)^2081*20000000000000^1569 ≤ 8817483348883^1569*500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269647191 500000000 8817483348883 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328117319/2500000000 : ℝ), (-2109533059/10000000000 : ℝ), (269647191/500000000 : ℝ)] ![(21608493055433/50000000000000 : ℝ), (12695597125227/100000000000000 : ℝ), (8817483348883/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328117319/2500000000 : ℝ)|^2081 ≤ (21608493055433/50000000000000 : ℝ)^1569
        have hw : |(1328117319/2500000000 : ℝ)|=(1328117319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109533059/10000000000 : ℝ)|^2081 ≤ (12695597125227/100000000000000 : ℝ)^1569
        have hw : |(-2109533059/10000000000 : ℝ)|=(2109533059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269647191/500000000 : ℝ)|^2081 ≤ (8817483348883/20000000000000 : ℝ)^1569
        have hw : |(269647191/500000000 : ℝ)|=(269647191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s7_6 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312469157/10000000000 : ℝ)*x 0 + (337058999/625000000 : ℝ)*x 1 + (-2109532997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312469157/10000000000 : ℝ)^2081 ≤ (21608492413449/50000000000000 : ℝ)^1569 := by
    have hnat : (5312469157 : ℕ)^2081*50000000000000^1569 ≤ 21608492413449^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312469157 10000000000 21608492413449 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337058999/625000000 : ℝ)^2081 ≤ (2204370926131/5000000000000 : ℝ)^1569 := by
    have hnat : (337058999 : ℕ)^2081*5000000000000^1569 ≤ 2204370926131^1569*625000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337058999 625000000 2204370926131 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109532997/10000000000 : ℝ)^2081 ≤ (6347798315169/50000000000000 : ℝ)^1569 := by
    have hnat : (2109532997 : ℕ)^2081*50000000000000^1569 ≤ 6347798315169^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109532997 10000000000 6347798315169 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312469157/10000000000 : ℝ), (337058999/625000000 : ℝ), (-2109532997/10000000000 : ℝ)] ![(21608492413449/50000000000000 : ℝ), (2204370926131/5000000000000 : ℝ), (6347798315169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312469157/10000000000 : ℝ)|^2081 ≤ (21608492413449/50000000000000 : ℝ)^1569
        have hw : |(5312469157/10000000000 : ℝ)|=(5312469157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337058999/625000000 : ℝ)|^2081 ≤ (2204370926131/5000000000000 : ℝ)^1569
        have hw : |(337058999/625000000 : ℝ)|=(337058999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2109532997/10000000000 : ℝ)|^2081 ≤ (6347798315169/50000000000000 : ℝ)^1569
        have hw : |(-2109532997/10000000000 : ℝ)|=(2109532997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s7_7 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4366233629/10000000000 : ℝ)*x 0 + (1123553089/2500000000 : ℝ)*x 1 + (4241909623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366233629/10000000000 : ℝ)^2081 ≤ (8329247867961/25000000000000 : ℝ)^1569 := by
    have hnat : (4366233629 : ℕ)^2081*25000000000000^1569 ≤ 8329247867961^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366233629 10000000000 8329247867961 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123553089/2500000000 : ℝ)^2081 ≤ (34618372037351/100000000000000 : ℝ)^1569 := by
    have hnat : (1123553089 : ℕ)^2081*100000000000000^1569 ≤ 34618372037351^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123553089 2500000000 34618372037351 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241909623/10000000000 : ℝ)^2081 ≤ (32064636473563/100000000000000 : ℝ)^1569 := by
    have hnat : (4241909623 : ℕ)^2081*100000000000000^1569 ≤ 32064636473563^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241909623 10000000000 32064636473563 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366233629/10000000000 : ℝ), (1123553089/2500000000 : ℝ), (4241909623/10000000000 : ℝ)] ![(8329247867961/25000000000000 : ℝ), (34618372037351/100000000000000 : ℝ), (32064636473563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366233629/10000000000 : ℝ)|^2081 ≤ (8329247867961/25000000000000 : ℝ)^1569
        have hw : |(4366233629/10000000000 : ℝ)|=(4366233629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123553089/2500000000 : ℝ)|^2081 ≤ (34618372037351/100000000000000 : ℝ)^1569
        have hw : |(1123553089/2500000000 : ℝ)|=(1123553089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241909623/10000000000 : ℝ)|^2081 ≤ (32064636473563/100000000000000 : ℝ)^1569
        have hw : |(4241909623/10000000000 : ℝ)|=(4241909623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5669/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3511/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11331/100000 : ℝ) ^ (8323/2048 : ℝ) ≤ (143409979558913/1000000000000000000 : ℝ) := by
    have hpowers : (11331/100000 : ℝ)^8323 ≤ (143409979558913/1000000000000000000 : ℝ)^2048 := by
      have hnat : (11331 : ℕ)^8323*1000000000000000000^2048 ≤ 143409979558913^2048*100000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11331 100000 143409979558913 1000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11331/100000 : ℝ)) (X := (143409979558913/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14051/100000 : ℝ) ^ (8323/2048 : ℝ) ≤ (34380497870812283/100000000000000000000 : ℝ) := by
    have hpowers : (14051/100000 : ℝ)^8323 ≤ (34380497870812283/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14051 : ℕ)^8323*100000000000000000000^2048 ≤ 34380497870812283^2048*100000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14051 100000 34380497870812283 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14051/100000 : ℝ)) (X := (34380497870812283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (500143409979558913/500000000000000000 : ℝ) ≤ (10000705687583081/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (500143409979558913/500000000000000000 : ℝ)^2048 ≤ (10000705687583081/10000000000000000 : ℝ)^8323 := by
      have hnat : (500143409979558913 : ℕ)^2048*10000000000000000^8323 ≤ 10000705687583081^8323*500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500143409979558913 500000000000000000 10000705687583081 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000705687583081/10000000000000000 : ℝ)) (X := (500143409979558913/500000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048721495826703583/100000000000000000000 : ℝ) ≤ (10001198645949321/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (100048721495826703583/100000000000000000000 : ℝ)^2048 ≤ (10001198645949321/10000000000000000 : ℝ)^8323 := by
      have hnat : (100048721495826703583 : ℕ)^2048*10000000000000000^8323 ≤ 10001198645949321^8323*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048721495826703583 100000000000000000000 10001198645949321 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001198645949321/10000000000000000 : ℝ)) (X := (100048721495826703583/100000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034380497870812283/50000000000000000000 : ℝ) ≤ (10001691604315561/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50034380497870812283/50000000000000000000 : ℝ)^2048 ≤ (10001691604315561/10000000000000000 : ℝ)^8323 := by
      have hnat : (50034380497870812283 : ℕ)^2048*10000000000000000^8323 ≤ 10001691604315561^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034380497870812283 50000000000000000000 10001691604315561 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001691604315561/10000000000000000 : ℝ)) (X := (50034380497870812283/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(143409979558913/1000000000000000000 : ℝ) ≤ ((169942175298314059/170000000000000000 : ℝ)+2*(3080989789/1700000000000 : ℝ)*(11331/100000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (169942175298314059/170000000000000000 : ℝ)+2*(3080989789/1700000000000 : ℝ)*(11331/100000 : ℝ)=(10000705687583081/10000000000000000 : ℝ) by norm_num, show 1+2*(143409979558913/1000000000000000000 : ℝ)=(500143409979558913/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34380497870812283/100000000000000000000 : ℝ)+(143409979558913/1000000000000000000 : ℝ) ≤ ((169942175298314059/170000000000000000 : ℝ)+(3080989789/1700000000000 : ℝ)*((14051/100000 : ℝ)+(11331/100000 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (169942175298314059/170000000000000000 : ℝ)+(3080989789/1700000000000 : ℝ)*((14051/100000 : ℝ)+(11331/100000 : ℝ))=(10001198645949321/10000000000000000 : ℝ) by norm_num, show 1+(34380497870812283/100000000000000000000 : ℝ)+(143409979558913/1000000000000000000 : ℝ)=(100048721495826703583/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34380497870812283/100000000000000000000 : ℝ) ≤ ((169942175298314059/170000000000000000 : ℝ)+2*(3080989789/1700000000000 : ℝ)*(14051/100000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (169942175298314059/170000000000000000 : ℝ)+2*(3080989789/1700000000000 : ℝ)*(14051/100000 : ℝ)=(10001691604315561/10000000000000000 : ℝ) by norm_num, show 1+2*(34380497870812283/100000000000000000000 : ℝ)=(50034380497870812283/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (169942175298314059/170000000000000000 : ℝ)*(X 1 0+X 2 0)+(3080989789/1700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (169942175298314059/170000000000000000 : ℝ)) (alpha := (3080989789/1700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (169942175298314059/170000000000000000 : ℝ)*(X 0 1+X 2 1)+(3080989789/1700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (169942175298314059/170000000000000000 : ℝ)) (alpha := (3080989789/1700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (169942175298314059/170000000000000000 : ℝ)*(X 0 2+X 1 2)+(3080989789/1700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (169942175298314059/170000000000000000 : ℝ)) (alpha := (3080989789/1700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2172153629/10000000000 : ℝ)*X 0 0+(5393265427/10000000000 : ℝ)*X 0 1+(2632764639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336201507/2500000000 : ℝ)*X 1 0+(-2236946853/10000000000 : ℝ)*X 1 1+(5265529289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334050377/625000000 : ℝ)*X 2 0+(5265529291/10000000000 : ℝ)*X 2 1+(-559236711/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183111719/5000000000 : ℝ)*X 0 0+(530158787/1250000000 : ℝ)*X 0 1+(4494849807/10000000000 : ℝ)*X 0 2+(2183111719/5000000000 : ℝ)*X 1 0+(530158787/1250000000 : ℝ)*X 1 1+(4494849807/10000000000 : ℝ)*X 1 2+(2183111719/5000000000 : ℝ)*X 2 0+(530158787/1250000000 : ℝ)*X 2 1+(4494849807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2172158489/10000000000 : ℝ)*X 0 0+(658231327/1250000000 : ℝ)*X 0 1+(2696471487/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328117319/2500000000 : ℝ)*X 1 0+(-2109533059/10000000000 : ℝ)*X 1 1+(269647191/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312469157/10000000000 : ℝ)*X 2 0+(337058999/625000000 : ℝ)*X 2 1+(-2109532997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366233629/10000000000 : ℝ)*X 0 0+(1123553089/2500000000 : ℝ)*X 0 1+(4241909623/10000000000 : ℝ)*X 0 2+(4366233629/10000000000 : ℝ)*X 1 0+(1123553089/2500000000 : ℝ)*X 1 1+(4241909623/10000000000 : ℝ)*X 1 2+(4366233629/10000000000 : ℝ)*X 2 0+(1123553089/2500000000 : ℝ)*X 2 1+(4241909623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (482806677068330237781/85000000000000000000000000 : ℝ) := by norm_num
    linear_combination (227445687/20000000000000 : ℝ)*(base19) + (107806477/10000000000000 : ℝ)*(base23) + (34753313/100000000000000 : ℝ)*(lower2) + (3401641/2500000000000 : ℝ)*(upper3) + (12834801/12500000000000 : ℝ)*(upper5) + (5886135253897553/100000000000000 : ℝ)*(major0) + (5886135253897553/100000000000000 : ℝ)*(major1) + (5886135253897553/100000000000000 : ℝ)*(major2) + (978583760861051/12500000000000 : ℝ)*(sp0) + (3914350601958329/50000000000000 : ℝ)*(sp1) + (7828701263080323/100000000000000 : ℝ)*(sp2) + (394355154806137/10000000000000 : ℝ)*(sp3) + (6450851337/20000000000000 : ℝ)*(sp4) + (16429252683/100000000000000 : ℝ)*(sp7) + (1971783988657027/50000000000000 : ℝ)*(f.failure) + (7828702341145093/100000000000000 : ℝ)*(f.sum) + (311793855367/85000000000000000000000000 : ℝ)*base65 + (77813774110702373/17000000000000000000000000000000 : ℝ)*base68 + (75438191883702373/17000000000000000000000000000000 : ℝ)*base70 + (90521720309702373/17000000000000000000000000000000 : ℝ)*base72 + (352647262173/85000000000000000000000000 : ℝ)*base74 + (145427413800297627/17000000000000000000000000000000 : ℝ)*base75 + (106969083186297627/17000000000000000000000000000000 : ℝ)*base77 + (135716378000297627/17000000000000000000000000000000 : ℝ)*base79 + (145219330039/42500000000000000000000000 : ℝ)*base82 + (6840651/500000000000000000000 : ℝ)*base89 + (6840651/500000000000000000000 : ℝ)*base91 + (6840651/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123108283199308605694977477/8500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (220130859/100000000000000 : ℝ)*(base19) + (849254077/100000000000000 : ℝ)*(base23) + (555577009/100000000000000 : ℝ)*(upper3) + (313683181/100000000000000 : ℝ)*(lower4) + (4149237/2500000000000 : ℝ)*(upper5) + (5915881655911099/100000000000000 : ℝ)*(major0) + (5915881655911099/100000000000000 : ℝ)*(major1) + (5915881655911099/100000000000000 : ℝ)*(major2) + (829943701/5000000000000 : ℝ)*(sp1) + (51904926521/100000000000000 : ℝ)*(sp2) + (786826548324667/10000000000000 : ℝ)*(sp4) + (786824866424179/10000000000000 : ℝ)*(sp5) + (983526591133259/12500000000000 : ℝ)*(sp6) + (1981748672898971/50000000000000 : ℝ)*(sp7) + (1981748672898971/50000000000000 : ℝ)*(f.failure) + (786826548324667/10000000000000 : ℝ)*(f.sum) + (9888427631/85000000000000000000000000 : ℝ)*base65 + (12911441872940841/17000000000000000000000000000000 : ℝ)*base67 + (43912288485059159/17000000000000000000000000000000 : ℝ)*base70 + (6980005090940841/17000000000000000000000000000000 : ℝ)*base71 + (107502249859/85000000000000000000000000 : ℝ)*base74 + (136083490514940841/17000000000000000000000000000000 : ℝ)*base75 + (87435944301059159/17000000000000000000000000000000 : ℝ)*base78 + (122396733309940841/17000000000000000000000000000000 : ℝ)*base79 + (417275542319/85000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3935523/500000000000000000000 : ℝ)*base89 + (3935523/500000000000000000000 : ℝ)*base91 + (3935523/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1131_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1131_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1131_s8_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-135759921/625000000 : ℝ)*x 0 + (539319467/1000000000 : ℝ)*x 1 + (1053119353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135759921/625000000 : ℝ)^2081 ≤ (105583083971/800000000000 : ℝ)^1569 := by
    have hnat : (135759921 : ℕ)^2081*800000000000^1569 ≤ 105583083971^1569*625000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135759921 625000000 105583083971 800000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539319467/1000000000 : ℝ)^2081 ≤ (44090136659179/100000000000000 : ℝ)^1569 := by
    have hnat : (539319467 : ℕ)^2081*100000000000000^1569 ≤ 44090136659179^1569*1000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539319467 1000000000 44090136659179 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053119353/2000000000 : ℝ)^2081 ≤ (42711977829539/100000000000000 : ℝ)^1569 := by
    have hnat : (1053119353 : ℕ)^2081*100000000000000^1569 ≤ 42711977829539^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053119353 2000000000 42711977829539 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135759921/625000000 : ℝ), (539319467/1000000000 : ℝ), (1053119353/2000000000 : ℝ)] ![(105583083971/800000000000 : ℝ), (44090136659179/100000000000000 : ℝ), (42711977829539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135759921/625000000 : ℝ)|^2081 ≤ (105583083971/800000000000 : ℝ)^1569
        have hw : |(-135759921/625000000 : ℝ)|=(135759921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539319467/1000000000 : ℝ)|^2081 ≤ (44090136659179/100000000000000 : ℝ)^1569
        have hw : |(539319467/1000000000 : ℝ)|=(539319467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053119353/2000000000 : ℝ)|^2081 ≤ (42711977829539/100000000000000 : ℝ)^1569
        have hw : |(1053119353/2000000000 : ℝ)|=(1053119353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s8_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672394273/5000000000 : ℝ)*x 0 + (-223688089/1000000000 : ℝ)*x 1 + (5265596741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672394273/5000000000 : ℝ)^2081 ≤ (21783022624639/50000000000000 : ℝ)^1569 := by
    have hnat : (2672394273 : ℕ)^2081*50000000000000^1569 ≤ 21783022624639^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672394273 5000000000 21783022624639 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223688089/1000000000 : ℝ)^2081 ≤ (6860988582551/50000000000000 : ℝ)^1569 := by
    have hnat : (223688089 : ℕ)^2081*50000000000000^1569 ≤ 6860988582551^1569*1000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223688089 1000000000 6860988582551 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265596741/10000000000 : ℝ)^2081 ≤ (5338997196417/12500000000000 : ℝ)^1569 := by
    have hnat : (5265596741 : ℕ)^2081*12500000000000^1569 ≤ 5338997196417^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265596741 10000000000 5338997196417 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672394273/5000000000 : ℝ), (-223688089/1000000000 : ℝ), (5265596741/10000000000 : ℝ)] ![(21783022624639/50000000000000 : ℝ), (6860988582551/50000000000000 : ℝ), (5338997196417/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672394273/5000000000 : ℝ)|^2081 ≤ (21783022624639/50000000000000 : ℝ)^1569
        have hw : |(2672394273/5000000000 : ℝ)|=(2672394273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223688089/1000000000 : ℝ)|^2081 ≤ (6860988582551/50000000000000 : ℝ)^1569
        have hw : |(-223688089/1000000000 : ℝ)|=(223688089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265596741/10000000000 : ℝ)|^2081 ≤ (5338997196417/12500000000000 : ℝ)^1569
        have hw : |(5265596741/10000000000 : ℝ)|=(5265596741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s8_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672394281/5000000000 : ℝ)*x 0 + (1316399187/2500000000 : ℝ)*x 1 + (-2236880859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672394281/5000000000 : ℝ)^2081 ≤ (21783022711127/50000000000000 : ℝ)^1569 := by
    have hnat : (2672394281 : ℕ)^2081*50000000000000^1569 ≤ 21783022711127^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672394281 5000000000 21783022711127 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316399187/2500000000 : ℝ)^2081 ≤ (8542395529329/20000000000000 : ℝ)^1569 := by
    have hnat : (1316399187 : ℕ)^2081*20000000000000^1569 ≤ 8542395529329^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316399187 2500000000 8542395529329 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236880859/10000000000 : ℝ)^2081 ≤ (13721976912879/100000000000000 : ℝ)^1569 := by
    have hnat : (2236880859 : ℕ)^2081*100000000000000^1569 ≤ 13721976912879^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236880859 10000000000 13721976912879 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672394281/5000000000 : ℝ), (1316399187/2500000000 : ℝ), (-2236880859/10000000000 : ℝ)] ![(21783022711127/50000000000000 : ℝ), (8542395529329/20000000000000 : ℝ), (13721976912879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672394281/5000000000 : ℝ)|^2081 ≤ (21783022711127/50000000000000 : ℝ)^1569
        have hw : |(2672394281/5000000000 : ℝ)|=(2672394281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316399187/2500000000 : ℝ)|^2081 ≤ (8542395529329/20000000000000 : ℝ)^1569
        have hw : |(1316399187/2500000000 : ℝ)|=(1316399187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2236880859/10000000000 : ℝ)|^2081 ≤ (13721976912879/100000000000000 : ℝ)^1569
        have hw : |(-2236880859/10000000000 : ℝ)|=(2236880859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s8_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2183113477/5000000000 : ℝ)*x 0 + (1060351761/2500000000 : ℝ)*x 1 + (2247356071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183113477/5000000000 : ℝ)^2081 ≤ (16658461958297/50000000000000 : ℝ)^1569 := by
    have hnat : (2183113477 : ℕ)^2081*50000000000000^1569 ≤ 16658461958297^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183113477 5000000000 16658461958297 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060351761/2500000000 : ℝ)^2081 ≤ (32059597872337/100000000000000 : ℝ)^1569 := by
    have hnat : (1060351761 : ℕ)^2081*100000000000000^1569 ≤ 32059597872337^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060351761 2500000000 32059597872337 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247356071/5000000000 : ℝ)^2081 ≤ (34623478194239/100000000000000 : ℝ)^1569 := by
    have hnat : (2247356071 : ℕ)^2081*100000000000000^1569 ≤ 34623478194239^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247356071 5000000000 34623478194239 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183113477/5000000000 : ℝ), (1060351761/2500000000 : ℝ), (2247356071/5000000000 : ℝ)] ![(16658461958297/50000000000000 : ℝ), (32059597872337/100000000000000 : ℝ), (34623478194239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183113477/5000000000 : ℝ)|^2081 ≤ (16658461958297/50000000000000 : ℝ)^1569
        have hw : |(2183113477/5000000000 : ℝ)|=(2183113477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060351761/2500000000 : ℝ)|^2081 ≤ (32059597872337/100000000000000 : ℝ)^1569
        have hw : |(1060351761/2500000000 : ℝ)|=(1060351761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247356071/5000000000 : ℝ)|^2081 ≤ (34623478194239/100000000000000 : ℝ)^1569
        have hw : |(2247356071/5000000000 : ℝ)|=(2247356071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s8_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-135760233/625000000 : ℝ)*x 0 + (2632958567/5000000000 : ℝ)*x 1 + (2696436539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135760233/625000000 : ℝ)^2081 ≤ (13197925725137/100000000000000 : ℝ)^1569 := by
    have hnat : (135760233 : ℕ)^2081*100000000000000^1569 ≤ 13197925725137^1569*625000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135760233 625000000 13197925725137 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632958567/5000000000 : ℝ)^2081 ≤ (42715424549647/100000000000000 : ℝ)^1569 := by
    have hnat : (2632958567 : ℕ)^2081*100000000000000^1569 ≤ 42715424549647^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632958567 5000000000 42715424549647 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696436539/5000000000 : ℝ)^2081 ≤ (344426950867/781250000000 : ℝ)^1569 := by
    have hnat : (2696436539 : ℕ)^2081*781250000000^1569 ≤ 344426950867^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696436539 5000000000 344426950867 781250000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135760233/625000000 : ℝ), (2632958567/5000000000 : ℝ), (2696436539/5000000000 : ℝ)] ![(13197925725137/100000000000000 : ℝ), (42715424549647/100000000000000 : ℝ), (344426950867/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135760233/625000000 : ℝ)|^2081 ≤ (13197925725137/100000000000000 : ℝ)^1569
        have hw : |(-135760233/625000000 : ℝ)|=(135760233/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632958567/5000000000 : ℝ)|^2081 ≤ (42715424549647/100000000000000 : ℝ)^1569
        have hw : |(2632958567/5000000000 : ℝ)|=(2632958567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696436539/5000000000 : ℝ)|^2081 ≤ (344426950867/781250000000 : ℝ)^1569
        have hw : |(2696436539/5000000000 : ℝ)|=(2696436539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s8_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656243537/5000000000 : ℝ)*x 0 + (-2109605213/10000000000 : ℝ)*x 1 + (5392872991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656243537/5000000000 : ℝ)^2081 ≤ (10804294536271/25000000000000 : ℝ)^1569 := by
    have hnat : (2656243537 : ℕ)^2081*25000000000000^1569 ≤ 10804294536271^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656243537 5000000000 10804294536271 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109605213/10000000000 : ℝ)^2081 ≤ (3174043266813/25000000000000 : ℝ)^1569 := by
    have hnat : (2109605213 : ℕ)^2081*25000000000000^1569 ≤ 3174043266813^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109605213 10000000000 3174043266813 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392872991/10000000000 : ℝ)^2081 ≤ (2755415547979/6250000000000 : ℝ)^1569 := by
    have hnat : (5392872991 : ℕ)^2081*6250000000000^1569 ≤ 2755415547979^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392872991 10000000000 2755415547979 6250000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656243537/5000000000 : ℝ), (-2109605213/10000000000 : ℝ), (5392872991/10000000000 : ℝ)] ![(10804294536271/25000000000000 : ℝ), (3174043266813/25000000000000 : ℝ), (2755415547979/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656243537/5000000000 : ℝ)|^2081 ≤ (10804294536271/25000000000000 : ℝ)^1569
        have hw : |(2656243537/5000000000 : ℝ)|=(2656243537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109605213/10000000000 : ℝ)|^2081 ≤ (3174043266813/25000000000000 : ℝ)^1569
        have hw : |(-2109605213/10000000000 : ℝ)|=(2109605213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392872991/10000000000 : ℝ)|^2081 ≤ (2755415547979/6250000000000 : ℝ)^1569
        have hw : |(5392872991/10000000000 : ℝ)|=(5392872991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s8_6 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312488109/10000000000 : ℝ)*x 0 + (5392873059/10000000000 : ℝ)*x 1 + (-2109603723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312488109/10000000000 : ℝ)^2081 ≤ (2160859465619/5000000000000 : ℝ)^1569 := by
    have hnat : (5312488109 : ℕ)^2081*5000000000000^1569 ≤ 2160859465619^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312488109 10000000000 2160859465619 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392873059/10000000000 : ℝ)^2081 ≤ (22043324752483/50000000000000 : ℝ)^1569 := by
    have hnat : (5392873059 : ℕ)^2081*50000000000000^1569 ≤ 22043324752483^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392873059 10000000000 22043324752483 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109603723/10000000000 : ℝ)^2081 ≤ (507846446953/4000000000000 : ℝ)^1569 := by
    have hnat : (2109603723 : ℕ)^2081*4000000000000^1569 ≤ 507846446953^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109603723 10000000000 507846446953 4000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312488109/10000000000 : ℝ), (5392873059/10000000000 : ℝ), (-2109603723/10000000000 : ℝ)] ![(2160859465619/5000000000000 : ℝ), (22043324752483/50000000000000 : ℝ), (507846446953/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312488109/10000000000 : ℝ)|^2081 ≤ (2160859465619/5000000000000 : ℝ)^1569
        have hw : |(5312488109/10000000000 : ℝ)|=(5312488109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392873059/10000000000 : ℝ)|^2081 ≤ (22043324752483/50000000000000 : ℝ)^1569
        have hw : |(5392873059/10000000000 : ℝ)|=(5392873059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2109603723/10000000000 : ℝ)|^2081 ≤ (507846446953/4000000000000 : ℝ)^1569
        have hw : |(-2109603723/10000000000 : ℝ)|=(2109603723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s8_7 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4366237547/10000000000 : ℝ)*x 0 + (2247038141/5000000000 : ℝ)*x 1 + (4242044331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366237547/10000000000 : ℝ)^2081 ≤ (16658515562257/50000000000000 : ℝ)^1569 := by
    have hnat : (4366237547 : ℕ)^2081*50000000000000^1569 ≤ 16658515562257^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366237547 10000000000 16658515562257 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247038141/5000000000 : ℝ)^2081 ≤ (17308490922021/50000000000000 : ℝ)^1569 := by
    have hnat : (2247038141 : ℕ)^2081*50000000000000^1569 ≤ 17308490922021^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247038141 5000000000 17308490922021 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242044331/10000000000 : ℝ)^2081 ≤ (16032993510253/50000000000000 : ℝ)^1569 := by
    have hnat : (4242044331 : ℕ)^2081*50000000000000^1569 ≤ 16032993510253^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242044331 10000000000 16032993510253 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366237547/10000000000 : ℝ), (2247038141/5000000000 : ℝ), (4242044331/10000000000 : ℝ)] ![(16658515562257/50000000000000 : ℝ), (17308490922021/50000000000000 : ℝ), (16032993510253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366237547/10000000000 : ℝ)|^2081 ≤ (16658515562257/50000000000000 : ℝ)^1569
        have hw : |(4366237547/10000000000 : ℝ)|=(4366237547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247038141/5000000000 : ℝ)|^2081 ≤ (17308490922021/50000000000000 : ℝ)^1569
        have hw : |(2247038141/5000000000 : ℝ)|=(2247038141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242044331/10000000000 : ℝ)|^2081 ≤ (16032993510253/50000000000000 : ℝ)^1569
        have hw : |(4242044331/10000000000 : ℝ)|=(4242044331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7021/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5669/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5669/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5669/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5669/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5669/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5669/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5669/50000 : ℝ) ^ (8323/2048 : ℝ) ≤ (2875407347857329/20000000000000000000 : ℝ) := by
    have hpowers : (5669/50000 : ℝ)^8323 ≤ (2875407347857329/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5669 : ℕ)^8323*20000000000000000000^2048 ≤ 2875407347857329^2048*50000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5669 50000 2875407347857329 20000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5669/50000 : ℝ)) (X := (2875407347857329/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3511/25000 : ℝ) ^ (8323/2048 : ℝ) ≤ (343109439784543/1000000000000000000 : ℝ) := by
    have hpowers : (3511/25000 : ℝ)^8323 ≤ (343109439784543/1000000000000000000 : ℝ)^2048 := by
      have hnat : (3511 : ℕ)^8323*1000000000000000000^2048 ≤ 343109439784543^2048*25000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3511 25000 343109439784543 1000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3511/25000 : ℝ)) (X := (343109439784543/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002875407347857329/10000000000000000000 : ℝ) ≤ (625044216298543/625000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (10002875407347857329/10000000000000000000 : ℝ)^2048 ≤ (625044216298543/625000000000000 : ℝ)^8323 := by
      have hnat : (10002875407347857329 : ℕ)^2048*625000000000000^8323 ≤ 625044216298543^8323*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002875407347857329 10000000000000000000 625044216298543 625000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625044216298543/625000000000000 : ℝ)) (X := (10002875407347857329/10000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009737596143548189/20000000000000000000 : ℝ) ≤ (5000598910781043/5000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (20009737596143548189/20000000000000000000 : ℝ)^2048 ≤ (5000598910781043/5000000000000000 : ℝ)^8323 := by
      have hnat : (20009737596143548189 : ℕ)^2048*5000000000000000^8323 ≤ 5000598910781043^8323*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009737596143548189 20000000000000000000 5000598910781043 5000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000598910781043/5000000000000000 : ℝ)) (X := (20009737596143548189/20000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (500343109439784543/500000000000000000 : ℝ) ≤ (2500422045586871/2500000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (500343109439784543/500000000000000000 : ℝ)^2048 ≤ (2500422045586871/2500000000000000 : ℝ)^8323 := by
      have hnat : (500343109439784543 : ℕ)^2048*2500000000000000^8323 ≤ 2500422045586871^8323*500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500343109439784543 500000000000000000 2500422045586871 2500000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500422045586871/2500000000000000 : ℝ)) (X := (500343109439784543/500000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2875407347857329/20000000000000000000 : ℝ) ≤ ((61479079472027347/61500000000000000 : ℝ)+2*(22289126609/12300000000000 : ℝ)*(5669/50000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (61479079472027347/61500000000000000 : ℝ)+2*(22289126609/12300000000000 : ℝ)*(5669/50000 : ℝ)=(625044216298543/625000000000000 : ℝ) by norm_num, show 1+2*(2875407347857329/20000000000000000000 : ℝ)=(10002875407347857329/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(343109439784543/1000000000000000000 : ℝ)+(2875407347857329/20000000000000000000 : ℝ) ≤ ((61479079472027347/61500000000000000 : ℝ)+(22289126609/12300000000000 : ℝ)*((3511/25000 : ℝ)+(5669/50000 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (61479079472027347/61500000000000000 : ℝ)+(22289126609/12300000000000 : ℝ)*((3511/25000 : ℝ)+(5669/50000 : ℝ))=(5000598910781043/5000000000000000 : ℝ) by norm_num, show 1+(343109439784543/1000000000000000000 : ℝ)+(2875407347857329/20000000000000000000 : ℝ)=(20009737596143548189/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(343109439784543/1000000000000000000 : ℝ) ≤ ((61479079472027347/61500000000000000 : ℝ)+2*(22289126609/12300000000000 : ℝ)*(3511/25000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (61479079472027347/61500000000000000 : ℝ)+2*(22289126609/12300000000000 : ℝ)*(3511/25000 : ℝ)=(2500422045586871/2500000000000000 : ℝ) by norm_num, show 1+2*(343109439784543/1000000000000000000 : ℝ)=(500343109439784543/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (61479079472027347/61500000000000000 : ℝ)*(X 1 0+X 2 0)+(22289126609/12300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (61479079472027347/61500000000000000 : ℝ)) (alpha := (22289126609/12300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (61479079472027347/61500000000000000 : ℝ)*(X 0 1+X 2 1)+(22289126609/12300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (61479079472027347/61500000000000000 : ℝ)) (alpha := (22289126609/12300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (61479079472027347/61500000000000000 : ℝ)*(X 0 2+X 1 2)+(22289126609/12300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (5669/50000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (61479079472027347/61500000000000000 : ℝ)) (alpha := (22289126609/12300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-135759921/625000000 : ℝ)*X 0 0+(539319467/1000000000 : ℝ)*X 0 1+(1053119353/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672394273/5000000000 : ℝ)*X 1 0+(-223688089/1000000000 : ℝ)*X 1 1+(5265596741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672394281/5000000000 : ℝ)*X 2 0+(1316399187/2500000000 : ℝ)*X 2 1+(-2236880859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183113477/5000000000 : ℝ)*X 0 0+(1060351761/2500000000 : ℝ)*X 0 1+(2247356071/5000000000 : ℝ)*X 0 2+(2183113477/5000000000 : ℝ)*X 1 0+(1060351761/2500000000 : ℝ)*X 1 1+(2247356071/5000000000 : ℝ)*X 1 2+(2183113477/5000000000 : ℝ)*X 2 0+(1060351761/2500000000 : ℝ)*X 2 1+(2247356071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-135760233/625000000 : ℝ)*X 0 0+(2632958567/5000000000 : ℝ)*X 0 1+(2696436539/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656243537/5000000000 : ℝ)*X 1 0+(-2109605213/10000000000 : ℝ)*X 1 1+(5392872991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312488109/10000000000 : ℝ)*X 2 0+(5392873059/10000000000 : ℝ)*X 2 1+(-2109603723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366237547/10000000000 : ℝ)*X 0 0+(2247038141/5000000000 : ℝ)*X 0 1+(4242044331/10000000000 : ℝ)*X 0 2+(4366237547/10000000000 : ℝ)*X 1 0+(2247038141/5000000000 : ℝ)*X 1 1+(4242044331/10000000000 : ℝ)*X 1 2+(4366237547/10000000000 : ℝ)*X 2 0+(2247038141/5000000000 : ℝ)*X 2 1+(4242044331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10029317584998609273385169/1025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (963874863/50000000000000 : ℝ)*(base19) + (1808980061/100000000000000 : ℝ)*(base23) + (76019431/100000000000000 : ℝ)*(lower2) + (111850117/50000000000000 : ℝ)*(upper3) + (172049181/100000000000000 : ℝ)*(upper5) + (5892542791134809/100000000000000 : ℝ)*(major0) + (5892542791134809/100000000000000 : ℝ)*(major1) + (5892542791134809/100000000000000 : ℝ)*(major2) + (7837171729799381/100000000000000 : ℝ)*(sp0) + (7837222456378487/100000000000000 : ℝ)*(sp1) + (979652821893519/12500000000000 : ℝ)*(sp2) + (15791334421253/400000000000 : ℝ)*(sp3) + (51420243/97656250000 : ℝ)*(sp4) + (27266671473/100000000000000 : ℝ)*(sp7) + (1973930435992361/50000000000000 : ℝ)*(f.failure) + (7837224384128213/100000000000000 : ℝ)*(f.sum) + (18959267219/38437500000000000000000000 : ℝ)*base66 + (96976200160573277/6150000000000000000000000000000 : ℝ)*base68 + (41184601132573277/6150000000000000000000000000000 : ℝ)*base70 + (89968914692923277/6150000000000000000000000000000 : ℝ)*base72 + (3517482085259/615000000000000000000000000 : ℝ)*base74 + (181805110694473277/6150000000000000000000000000000 : ℝ)*base76 + (67254673953223277/6150000000000000000000000000000 : ℝ)*base78 + (203444403229273277/6150000000000000000000000000000 : ℝ)*base80 + (8700437629/9609375000000000000000000 : ℝ)*base81 + (3950593/500000000000000000000 : ℝ)*base89 + (3950593/500000000000000000000 : ℝ)*base91 + (3950593/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1925880019342576874476101/1025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (880696889/100000000000000 : ℝ)*(base19) + (1229636303/50000000000000 : ℝ)*(base23) + (28978103/10000000000000 : ℝ)*(lower2) + (168610169/50000000000000 : ℝ)*(upper3) + (82784443/50000000000000 : ℝ)*(upper5) + (5922275854882017/100000000000000 : ℝ)*(major0) + (5922275854882017/100000000000000 : ℝ)*(major1) + (5922275854882017/100000000000000 : ℝ)*(major2) + (24237420491/25000000000000 : ℝ)*(sp2) + (3185630989/50000000000000 : ℝ)*(sp3) + (984596292872547/12500000000000 : ℝ)*(sp4) + (7876769462283487/100000000000000 : ℝ)*(sp5) + (1575334186805161/20000000000000 : ℝ)*(sp6) + (3967774932891421/100000000000000 : ℝ)*(sp7) + (1983890652076699/50000000000000 : ℝ)*(f.failure) + (984596292872547/12500000000000 : ℝ)*(f.sum) + (31096890349/51250000000000000000000000 : ℝ)*base65 + (318899904805367/2050000000000000000000000000000 : ℝ)*base68 + (29204120940344633/2050000000000000000000000000000 : ℝ)*base69 + (30415572987244633/2050000000000000000000000000000 : ℝ)*base71 + (38050893829/12812500000000000000000000 : ℝ)*base74 + (20436387752105367/2050000000000000000000000000000 : ℝ)*base76 + (13860999963494633/2050000000000000000000000000000 : ℝ)*base77 + (38910354820044633/2050000000000000000000000000000 : ℝ)*base79 + (445092725571/205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6398813/500000000000000000000 : ℝ)*base90 + (6398813/500000000000000000000 : ℝ)*base92 + (6398813/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1131_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1131_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1131_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1131_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1131_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1131_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1131_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

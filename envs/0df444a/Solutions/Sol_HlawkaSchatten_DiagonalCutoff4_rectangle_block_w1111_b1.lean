-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1111_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:05:01.852156+00:00
-- url     : https://prove2.me/submissions/786c9864-7bec-4359-ad33-368f4378973d

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
theorem support_rectangle_w1111_s3_0 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-217763799/1000000000 : ℝ)*x 0 + (42441099/78125000 : ℝ)*x 1 + (2614538587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217763799/1000000000 : ℝ)^519 ≤ (13221017663313/100000000000000 : ℝ)^391 := by
    have hnat : (217763799 : ℕ)^519*100000000000000^391 ≤ 13221017663313^391*1000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217763799 1000000000 13221017663313 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42441099/78125000 : ℝ)^519 ≤ (22244034558329/50000000000000 : ℝ)^391 := by
    have hnat : (42441099 : ℕ)^519*50000000000000^391 ≤ 22244034558329^391*78125000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42441099 78125000 22244034558329 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614538587/5000000000 : ℝ)^519 ≤ (4229091321027/10000000000000 : ℝ)^391 := by
    have hnat : (2614538587 : ℕ)^519*10000000000000^391 ≤ 4229091321027^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614538587 5000000000 4229091321027 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217763799/1000000000 : ℝ), (42441099/78125000 : ℝ), (2614538587/5000000000 : ℝ)] ![(13221017663313/100000000000000 : ℝ), (22244034558329/50000000000000 : ℝ), (4229091321027/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217763799/1000000000 : ℝ)|^519 ≤ (13221017663313/100000000000000 : ℝ)^391
        have hw : |(-217763799/1000000000 : ℝ)|=(217763799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42441099/78125000 : ℝ)|^519 ≤ (22244034558329/50000000000000 : ℝ)^391
        have hw : |(42441099/78125000 : ℝ)|=(42441099/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614538587/5000000000 : ℝ)|^519 ≤ (4229091321027/10000000000000 : ℝ)^391
        have hw : |(2614538587/5000000000 : ℝ)|=(2614538587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s3_1 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1070910437/2000000000 : ℝ)*x 0 + (-2281673307/10000000000 : ℝ)*x 1 + (5229077219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070910437/2000000000 : ℝ)^519 ≤ (43643182638543/100000000000000 : ℝ)^391 := by
    have hnat : (1070910437 : ℕ)^519*100000000000000^391 ≤ 43643182638543^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070910437 2000000000 43643182638543 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2281673307/10000000000 : ℝ)^519 ≤ (14065903655599/100000000000000 : ℝ)^391 := by
    have hnat : (2281673307 : ℕ)^519*100000000000000^391 ≤ 14065903655599^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281673307 10000000000 14065903655599 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229077219/10000000000 : ℝ)^519 ≤ (42290913693357/100000000000000 : ℝ)^391 := by
    have hnat : (5229077219 : ℕ)^519*100000000000000^391 ≤ 42290913693357^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229077219 10000000000 42290913693357 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070910437/2000000000 : ℝ), (-2281673307/10000000000 : ℝ), (5229077219/10000000000 : ℝ)] ![(43643182638543/100000000000000 : ℝ), (14065903655599/100000000000000 : ℝ), (42290913693357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070910437/2000000000 : ℝ)|^519 ≤ (43643182638543/100000000000000 : ℝ)^391
        have hw : |(1070910437/2000000000 : ℝ)|=(1070910437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2281673307/10000000000 : ℝ)|^519 ≤ (14065903655599/100000000000000 : ℝ)^391
        have hw : |(-2281673307/10000000000 : ℝ)|=(2281673307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229077219/10000000000 : ℝ)|^519 ≤ (42290913693357/100000000000000 : ℝ)^391
        have hw : |(5229077219/10000000000 : ℝ)|=(5229077219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s3_2 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5354552309/10000000000 : ℝ)*x 0 + (5229077319/10000000000 : ℝ)*x 1 + (-2281673011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354552309/10000000000 : ℝ)^519 ≤ (43643183980089/100000000000000 : ℝ)^391 := by
    have hnat : (5354552309 : ℕ)^519*100000000000000^391 ≤ 43643183980089^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354552309 10000000000 43643183980089 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229077319/10000000000 : ℝ)^519 ≤ (42290914766883/100000000000000 : ℝ)^391 := by
    have hnat : (5229077319 : ℕ)^519*100000000000000^391 ≤ 42290914766883^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229077319 10000000000 42290914766883 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2281673011/10000000000 : ℝ)^519 ≤ (562636049339/4000000000000 : ℝ)^391 := by
    have hnat : (2281673011 : ℕ)^519*4000000000000^391 ≤ 562636049339^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281673011 10000000000 562636049339 4000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354552309/10000000000 : ℝ), (5229077319/10000000000 : ℝ), (-2281673011/10000000000 : ℝ)] ![(43643183980089/100000000000000 : ℝ), (42290914766883/100000000000000 : ℝ), (562636049339/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354552309/10000000000 : ℝ)|^519 ≤ (43643183980089/100000000000000 : ℝ)^391
        have hw : |(5354552309/10000000000 : ℝ)|=(5354552309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229077319/10000000000 : ℝ)|^519 ≤ (42290914766883/100000000000000 : ℝ)^391
        have hw : |(5229077319/10000000000 : ℝ)|=(5229077319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2281673011/10000000000 : ℝ)|^519 ≤ (562636049339/4000000000000 : ℝ)^391
        have hw : |(-2281673011/10000000000 : ℝ)|=(2281673011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s3_3 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4366593487/10000000000 : ℝ)*x 0 + (2085072099/5000000000 : ℝ)*x 1 + (4572310737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366593487/10000000000 : ℝ)^519 ≤ (3329184284461/10000000000000 : ℝ)^391 := by
    have hnat : (4366593487 : ℕ)^519*10000000000000^391 ≤ 3329184284461^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366593487 10000000000 3329184284461 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085072099/5000000000 : ℝ)^519 ≤ (3131854313877/10000000000000 : ℝ)^391 := by
    have hnat : (2085072099 : ℕ)^519*10000000000000^391 ≤ 3131854313877^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085072099 5000000000 3131854313877 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4572310737/10000000000 : ℝ)^519 ≤ (17694806996793/50000000000000 : ℝ)^391 := by
    have hnat : (4572310737 : ℕ)^519*50000000000000^391 ≤ 17694806996793^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572310737 10000000000 17694806996793 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366593487/10000000000 : ℝ), (2085072099/5000000000 : ℝ), (4572310737/10000000000 : ℝ)] ![(3329184284461/10000000000000 : ℝ), (3131854313877/10000000000000 : ℝ), (17694806996793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366593487/10000000000 : ℝ)|^519 ≤ (3329184284461/10000000000000 : ℝ)^391
        have hw : |(4366593487/10000000000 : ℝ)|=(4366593487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085072099/5000000000 : ℝ)|^519 ≤ (3131854313877/10000000000000 : ℝ)^391
        have hw : |(2085072099/5000000000 : ℝ)|=(2085072099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4572310737/10000000000 : ℝ)|^519 ≤ (17694806996793/50000000000000 : ℝ)^391
        have hw : |(4572310737/10000000000 : ℝ)|=(4572310737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s3_4 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-435531519/2000000000 : ℝ)*x 0 + (2614942009/5000000000 : ℝ)*x 1 + (5431649269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435531519/2000000000 : ℝ)^519 ≤ (1322117565611/10000000000000 : ℝ)^391 := by
    have hnat : (435531519 : ℕ)^519*10000000000000^391 ≤ 1322117565611^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435531519 2000000000 1322117565611 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614942009/5000000000 : ℝ)^519 ≤ (1057489377751/2500000000000 : ℝ)^391 := by
    have hnat : (2614942009 : ℕ)^519*2500000000000^391 ≤ 1057489377751^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614942009 5000000000 1057489377751 2500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431649269/10000000000 : ℝ)^519 ≤ (44479249218767/100000000000000 : ℝ)^391 := by
    have hnat : (5431649269 : ℕ)^519*100000000000000^391 ≤ 44479249218767^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431649269 10000000000 44479249218767 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435531519/2000000000 : ℝ), (2614942009/5000000000 : ℝ), (5431649269/10000000000 : ℝ)] ![(1322117565611/10000000000000 : ℝ), (1057489377751/2500000000000 : ℝ), (44479249218767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435531519/2000000000 : ℝ)|^519 ≤ (1322117565611/10000000000000 : ℝ)^391
        have hw : |(-435531519/2000000000 : ℝ)|=(435531519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614942009/5000000000 : ℝ)|^519 ≤ (1057489377751/2500000000000 : ℝ)^391
        have hw : |(2614942009/5000000000 : ℝ)|=(2614942009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431649269/10000000000 : ℝ)|^519 ≤ (44479249218767/100000000000000 : ℝ)^391
        have hw : |(5431649269/10000000000 : ℝ)|=(5431649269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s3_5 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1060628787/2000000000 : ℝ)*x 0 + (-2079101109/10000000000 : ℝ)*x 1 + (1357912361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060628787/2000000000 : ℝ)^519 ≤ (43087876885193/100000000000000 : ℝ)^391 := by
    have hnat : (1060628787 : ℕ)^519*100000000000000^391 ≤ 43087876885193^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060628787 2000000000 43087876885193 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079101109/10000000000 : ℝ)^519 ≤ (12432871984913/100000000000000 : ℝ)^391 := by
    have hnat : (2079101109 : ℕ)^519*100000000000000^391 ≤ 12432871984913^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079101109 10000000000 12432871984913 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357912361/2500000000 : ℝ)^519 ≤ (44479251120959/100000000000000 : ℝ)^391 := by
    have hnat : (1357912361 : ℕ)^519*100000000000000^391 ≤ 44479251120959^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357912361 2500000000 44479251120959 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060628787/2000000000 : ℝ), (-2079101109/10000000000 : ℝ), (1357912361/2500000000 : ℝ)] ![(43087876885193/100000000000000 : ℝ), (12432871984913/100000000000000 : ℝ), (44479251120959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060628787/2000000000 : ℝ)|^519 ≤ (43087876885193/100000000000000 : ℝ)^391
        have hw : |(1060628787/2000000000 : ℝ)|=(1060628787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079101109/10000000000 : ℝ)|^519 ≤ (12432871984913/100000000000000 : ℝ)^391
        have hw : |(-2079101109/10000000000 : ℝ)|=(2079101109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357912361/2500000000 : ℝ)|^519 ≤ (44479251120959/100000000000000 : ℝ)^391
        have hw : |(1357912361/2500000000 : ℝ)|=(1357912361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s3_6 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2651571987/5000000000 : ℝ)*x 0 + (1357912321/2500000000 : ℝ)*x 1 + (-83164051/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651571987/5000000000 : ℝ)^519 ≤ (215439386529/500000000000 : ℝ)^391 := by
    have hnat : (2651571987 : ℕ)^519*500000000000^391 ≤ 215439386529^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651571987 5000000000 215439386529 500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357912321/2500000000 : ℝ)^519 ≤ (11119812345453/25000000000000 : ℝ)^391 := by
    have hnat : (1357912321 : ℕ)^519*25000000000000^391 ≤ 11119812345453^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357912321 2500000000 11119812345453 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83164051/400000000 : ℝ)^519 ≤ (6216436651273/50000000000000 : ℝ)^391 := by
    have hnat : (83164051 : ℕ)^519*50000000000000^391 ≤ 6216436651273^391*400000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83164051 400000000 6216436651273 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651571987/5000000000 : ℝ), (1357912321/2500000000 : ℝ), (-83164051/400000000 : ℝ)] ![(215439386529/500000000000 : ℝ), (11119812345453/25000000000000 : ℝ), (6216436651273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651571987/5000000000 : ℝ)|^519 ≤ (215439386529/500000000000 : ℝ)^391
        have hw : |(2651571987/5000000000 : ℝ)|=(2651571987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357912321/2500000000 : ℝ)|^519 ≤ (11119812345453/25000000000000 : ℝ)^391
        have hw : |(1357912321/2500000000 : ℝ)|=(1357912321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83164051/400000000 : ℝ)|^519 ≤ (6216436651273/50000000000000 : ℝ)^391
        have hw : |(-83164051/400000000 : ℝ)|=(83164051/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s3_7 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (54582903/125000000 : ℝ)*x 0 + (4570716037/10000000000 : ℝ)*x 1 + (4171748157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54582903/125000000 : ℝ)^519 ≤ (166461175151/500000000000 : ℝ)^391 := by
    have hnat : (54582903 : ℕ)^519*500000000000^391 ≤ 166461175151^391*125000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54582903 125000000 166461175151 500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4570716037/10000000000 : ℝ)^519 ≤ (17686615657951/50000000000000 : ℝ)^391 := by
    have hnat : (4570716037 : ℕ)^519*50000000000000^391 ≤ 17686615657951^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570716037 10000000000 17686615657951 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171748157/10000000000 : ℝ)^519 ≤ (31334533625413/100000000000000 : ℝ)^391 := by
    have hnat : (4171748157 : ℕ)^519*100000000000000^391 ≤ 31334533625413^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171748157 10000000000 31334533625413 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54582903/125000000 : ℝ), (4570716037/10000000000 : ℝ), (4171748157/10000000000 : ℝ)] ![(166461175151/500000000000 : ℝ), (17686615657951/50000000000000 : ℝ), (31334533625413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54582903/125000000 : ℝ)|^519 ≤ (166461175151/500000000000 : ℝ)^391
        have hw : |(54582903/125000000 : ℝ)|=(54582903/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4570716037/10000000000 : ℝ)|^519 ≤ (17686615657951/50000000000000 : ℝ)^391
        have hw : |(4570716037/10000000000 : ℝ)|=(4570716037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171748157/10000000000 : ℝ)|^519 ≤ (31334533625413/100000000000000 : ℝ)^391
        have hw : |(4171748157/10000000000 : ℝ)|=(4171748157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1111_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16597/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10541/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3711/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16597/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (279/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16597/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (279/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16597/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (279/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16597/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (279/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16597/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (279/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16597/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (279/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (279/3125 : ℝ) ^ (8303/2048 : ℝ) ≤ (1114752406081061/20000000000000000000 : ℝ) := by
    have hpowers : (279/3125 : ℝ)^8303 ≤ (1114752406081061/20000000000000000000 : ℝ)^2048 := by
      have hnat : (279 : ℕ)^8303*20000000000000000000^2048 ≤ 1114752406081061^2048*3125^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        279 3125 1114752406081061 20000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (279/3125 : ℝ)) (X := (1114752406081061/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16597/100000 : ℝ) ^ (8303/2048 : ℝ) ≤ (860507385923109/1250000000000000000 : ℝ) := by
    have hpowers : (16597/100000 : ℝ)^8303 ≤ (860507385923109/1250000000000000000 : ℝ)^2048 := by
      have hnat : (16597 : ℕ)^8303*1250000000000000000^2048 ≤ 860507385923109^2048*100000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16597 100000 860507385923109 1250000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16597/100000 : ℝ)) (X := (860507385923109/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001114752406081061/10000000000000000000 : ℝ) ≤ (5000137475434863/5000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (10001114752406081061/10000000000000000000 : ℝ)^2048 ≤ (5000137475434863/5000000000000000 : ℝ)^8303 := by
      have hnat : (10001114752406081061 : ℕ)^2048*5000000000000000^8303 ≤ 5000137475434863^8303*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001114752406081061 10000000000000000000 5000137475434863 5000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000137475434863/5000000000000000 : ℝ)) (X := (10001114752406081061/10000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002976574116170161/4000000000000000000 : ℝ) ≤ (2500458743513893/2500000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (4002976574116170161/4000000000000000000 : ℝ)^2048 ≤ (2500458743513893/2500000000000000 : ℝ)^8303 := by
      have hnat : (4002976574116170161 : ℕ)^2048*2500000000000000^8303 ≤ 2500458743513893^8303*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002976574116170161 4000000000000000000 2500458743513893 2500000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500458743513893/2500000000000000 : ℝ)) (X := (4002976574116170161/4000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (625860507385923109/625000000000000000 : ℝ) ≤ (5001697498620709/5000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (625860507385923109/625000000000000000 : ℝ)^2048 ≤ (5001697498620709/5000000000000000 : ℝ)^8303 := by
      have hnat : (625860507385923109 : ℕ)^2048*5000000000000000^8303 ≤ 5001697498620709^8303*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625860507385923109 625000000000000000 5001697498620709 5000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001697498620709/5000000000000000 : ℝ)) (X := (625860507385923109/625000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1114752406081061/20000000000000000000 : ℝ) ≤ ((38332126412106731259/38345000000000000000 : ℝ)+2*(780011592923/383450000000000 : ℝ)*(279/3125 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (38332126412106731259/38345000000000000000 : ℝ)+2*(780011592923/383450000000000 : ℝ)*(279/3125 : ℝ)=(5000137475434863/5000000000000000 : ℝ) by norm_num, show 1+2*(1114752406081061/20000000000000000000 : ℝ)=(10001114752406081061/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(860507385923109/1250000000000000000 : ℝ)+(1114752406081061/20000000000000000000 : ℝ) ≤ ((38332126412106731259/38345000000000000000 : ℝ)+(780011592923/383450000000000 : ℝ)*((16597/100000 : ℝ)+(279/3125 : ℝ)))^(8303/2048 : ℝ) := by
    rw [show (38332126412106731259/38345000000000000000 : ℝ)+(780011592923/383450000000000 : ℝ)*((16597/100000 : ℝ)+(279/3125 : ℝ))=(2500458743513893/2500000000000000 : ℝ) by norm_num, show 1+(860507385923109/1250000000000000000 : ℝ)+(1114752406081061/20000000000000000000 : ℝ)=(4002976574116170161/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(860507385923109/1250000000000000000 : ℝ) ≤ ((38332126412106731259/38345000000000000000 : ℝ)+2*(780011592923/383450000000000 : ℝ)*(16597/100000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (38332126412106731259/38345000000000000000 : ℝ)+2*(780011592923/383450000000000 : ℝ)*(16597/100000 : ℝ)=(5001697498620709/5000000000000000 : ℝ) by norm_num, show 1+2*(860507385923109/1250000000000000000 : ℝ)=(625860507385923109/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38332126412106731259/38345000000000000000 : ℝ)*(X 1 0+X 2 0)+(780011592923/383450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (279/3125 : ℝ)) (hi := (16597/100000 : ℝ)) (c := (38332126412106731259/38345000000000000000 : ℝ)) (alpha := (780011592923/383450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38332126412106731259/38345000000000000000 : ℝ)*(X 0 1+X 2 1)+(780011592923/383450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (279/3125 : ℝ)) (hi := (16597/100000 : ℝ)) (c := (38332126412106731259/38345000000000000000 : ℝ)) (alpha := (780011592923/383450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38332126412106731259/38345000000000000000 : ℝ)*(X 0 2+X 1 2)+(780011592923/383450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (279/3125 : ℝ)) (hi := (16597/100000 : ℝ)) (c := (38332126412106731259/38345000000000000000 : ℝ)) (alpha := (780011592923/383450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-217763799/1000000000 : ℝ)*X 0 0+(42441099/78125000 : ℝ)*X 0 1+(2614538587/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070910437/2000000000 : ℝ)*X 1 0+(-2281673307/10000000000 : ℝ)*X 1 1+(5229077219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354552309/10000000000 : ℝ)*X 2 0+(5229077319/10000000000 : ℝ)*X 2 1+(-2281673011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366593487/10000000000 : ℝ)*X 0 0+(2085072099/5000000000 : ℝ)*X 0 1+(4572310737/10000000000 : ℝ)*X 0 2+(4366593487/10000000000 : ℝ)*X 1 0+(2085072099/5000000000 : ℝ)*X 1 1+(4572310737/10000000000 : ℝ)*X 1 2+(4366593487/10000000000 : ℝ)*X 2 0+(2085072099/5000000000 : ℝ)*X 2 1+(4572310737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-435531519/2000000000 : ℝ)*X 0 0+(2614942009/5000000000 : ℝ)*X 0 1+(5431649269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060628787/2000000000 : ℝ)*X 1 0+(-2079101109/10000000000 : ℝ)*X 1 1+(1357912361/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651571987/5000000000 : ℝ)*X 2 0+(1357912321/2500000000 : ℝ)*X 2 1+(-83164051/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((54582903/125000000 : ℝ)*X 0 0+(4570716037/10000000000 : ℝ)*X 0 1+(4171748157/10000000000 : ℝ)*X 0 2+(54582903/125000000 : ℝ)*X 1 0+(4570716037/10000000000 : ℝ)*X 1 1+(4171748157/10000000000 : ℝ)*X 1 2+(54582903/125000000 : ℝ)*X 2 0+(4570716037/10000000000 : ℝ)*X 2 1+(4171748157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1379290401541488182450178177/479312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1055460533/100000000000000 : ℝ)*(base19) + (1002077397/100000000000000 : ℝ)*(base23) + (22960333/25000000000000 : ℝ)*(lower2) + (176525163/100000000000000 : ℝ)*(upper5) + (925426760727201/25000000000000 : ℝ)*(major0) + (925426760727201/25000000000000 : ℝ)*(major1) + (925426760727201/25000000000000 : ℝ)*(major2) + (4916837978815159/100000000000000 : ℝ)*(sp0) + (4916862873521499/100000000000000 : ℝ)*(sp1) + (4916863371959077/100000000000000 : ℝ)*(sp2) + (2486541463365781/100000000000000 : ℝ)*(sp3) + (5279044263/20000000000000 : ℝ)*(sp4) + (445054441/100000000000000 : ℝ)*(sp5) + (8152493903/100000000000000 : ℝ)*(sp7) + (621637403964921/25000000000000 : ℝ)*(f.failure) + (2458432187018237/50000000000000 : ℝ)*(f.sum) + (14168173624107/4793125000000000000000000000 : ℝ)*base66 + (5870820454394798941/958625000000000000000000000000000 : ℝ)*base68 + (973152798662048941/958625000000000000000000000000000 : ℝ)*base70 + (4532302096938548941/958625000000000000000000000000000 : ℝ)*base72 + (268785878849331/38345000000000000000000000000 : ℝ)*base74 + (16732686723388451059/958625000000000000000000000000000 : ℝ)*base75 + (5447758433021923941/958625000000000000000000000000000 : ℝ)*base78 + (10597873855467076059/958625000000000000000000000000000 : ℝ)*base79 + (87145526959561/38345000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (596541/2500000000000000000000 : ℝ)*base89 + (596541/2500000000000000000000 : ℝ)*base91 + (596541/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4598483093027506029607319901/958625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (863020103/100000000000000 : ℝ)*(base19) + (1108635657/100000000000000 : ℝ)*(base23) + (67153361/50000000000000 : ℝ)*(upper3) + (102948031/100000000000000 : ℝ)*(lower4) + (12489521/25000000000000 : ℝ)*(upper5) + (3731359359654587/100000000000000 : ℝ)*(major0) + (3731359359654587/100000000000000 : ℝ)*(major1) + (3731359359654587/100000000000000 : ℝ)*(major2) + (8557083771/50000000000000 : ℝ)*(sp1) + (18665650361/100000000000000 : ℝ)*(sp2) + (2478125288625777/50000000000000 : ℝ)*(sp4) + (4956232600063909/100000000000000 : ℝ)*(sp5) + (154882212592673/3125000000000 : ℝ)*(sp6) + (626616995539761/25000000000000 : ℝ)*(sp7) + (626616995539761/25000000000000 : ℝ)*(f.failure) + (2478125288625777/50000000000000 : ℝ)*(f.sum) + (2264663801281/4793125000000000000000000000 : ℝ)*base66 + (4960254985955735033/3834500000000000000000000000000000 : ℝ)*base67 + (6337441221732735033/3834500000000000000000000000000000 : ℝ)*base69 + (4907925008453235033/3834500000000000000000000000000000 : ℝ)*base71 + (59681388368817/38345000000000000000000000000 : ℝ)*base73 + (4832291578086735033/3834500000000000000000000000000000 : ℝ)*base75 + (21739520256712764967/3834500000000000000000000000000000 : ℝ)*base78 + (8219294656976235033/3834500000000000000000000000000000 : ℝ)*base79 + (171834386235663/38345000000000000000000000000 : ℝ)*base82 + (19596181/2500000000000000000000 : ℝ)*base89 + (19596181/2500000000000000000000 : ℝ)*base91 + (19596181/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1111_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16597/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10541/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3711/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1111_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1111_s4_0 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090451151/5000000000 : ℝ)*x 0 + (5403420209/10000000000 : ℝ)*x 1 + (1051196641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090451151/5000000000 : ℝ)^519 ≤ (3311832629601/25000000000000 : ℝ)^391 := by
    have hnat : (1090451151 : ℕ)^519*25000000000000^391 ≤ 3311832629601^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090451151 5000000000 3311832629601 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403420209/10000000000 : ℝ)^519 ≤ (44172670002159/100000000000000 : ℝ)^391 := by
    have hnat : (5403420209 : ℕ)^519*100000000000000^391 ≤ 44172670002159^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403420209 10000000000 44172670002159 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051196641/2000000000 : ℝ)^519 ≤ (42579999469337/100000000000000 : ℝ)^391 := by
    have hnat : (1051196641 : ℕ)^519*100000000000000^391 ≤ 42579999469337^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051196641 2000000000 42579999469337 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090451151/5000000000 : ℝ), (5403420209/10000000000 : ℝ), (1051196641/2000000000 : ℝ)] ![(3311832629601/25000000000000 : ℝ), (44172670002159/100000000000000 : ℝ), (42579999469337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090451151/5000000000 : ℝ)|^519 ≤ (3311832629601/25000000000000 : ℝ)^391
        have hw : |(-1090451151/5000000000 : ℝ)|=(1090451151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403420209/10000000000 : ℝ)|^519 ≤ (44172670002159/100000000000000 : ℝ)^391
        have hw : |(5403420209/10000000000 : ℝ)|=(5403420209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051196641/2000000000 : ℝ)|^519 ≤ (42579999469337/100000000000000 : ℝ)^391
        have hw : |(1051196641/2000000000 : ℝ)|=(1051196641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s4_1 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2673661581/5000000000 : ℝ)*x 0 + (-563963127/2500000000 : ℝ)*x 1 + (2627991723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673661581/5000000000 : ℝ)^519 ≤ (4356498971459/10000000000000 : ℝ)^391 := by
    have hnat : (2673661581 : ℕ)^519*10000000000000^391 ≤ 4356498971459^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673661581 5000000000 4356498971459 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563963127/2500000000 : ℝ)^519 ≤ (1731876026629/12500000000000 : ℝ)^391 := by
    have hnat : (563963127 : ℕ)^519*12500000000000^391 ≤ 1731876026629^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563963127 2500000000 1731876026629 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627991723/5000000000 : ℝ)^519 ≤ (21290001030443/50000000000000 : ℝ)^391 := by
    have hnat : (2627991723 : ℕ)^519*50000000000000^391 ≤ 21290001030443^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627991723 5000000000 21290001030443 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673661581/5000000000 : ℝ), (-563963127/2500000000 : ℝ), (2627991723/5000000000 : ℝ)] ![(4356498971459/10000000000000 : ℝ), (1731876026629/12500000000000 : ℝ), (21290001030443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673661581/5000000000 : ℝ)|^519 ≤ (4356498971459/10000000000000 : ℝ)^391
        have hw : |(2673661581/5000000000 : ℝ)|=(2673661581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-563963127/2500000000 : ℝ)|^519 ≤ (1731876026629/12500000000000 : ℝ)^391
        have hw : |(-563963127/2500000000 : ℝ)|=(563963127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627991723/5000000000 : ℝ)|^519 ≤ (21290001030443/50000000000000 : ℝ)^391
        have hw : |(2627991723/5000000000 : ℝ)|=(2627991723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s4_2 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347322951/10000000000 : ℝ)*x 0 + (2627991647/5000000000 : ℝ)*x 1 + (-2255852989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347322951/10000000000 : ℝ)^519 ≤ (43564987432807/100000000000000 : ℝ)^391 := by
    have hnat : (5347322951 : ℕ)^519*100000000000000^391 ≤ 43564987432807^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347322951 10000000000 43564987432807 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627991647/5000000000 : ℝ)^519 ≤ (21290000213191/50000000000000 : ℝ)^391 := by
    have hnat : (2627991647 : ℕ)^519*50000000000000^391 ≤ 21290000213191^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627991647 5000000000 21290000213191 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255852989/10000000000 : ℝ)^519 ≤ (3463753033587/25000000000000 : ℝ)^391 := by
    have hnat : (2255852989 : ℕ)^519*25000000000000^391 ≤ 3463753033587^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255852989 10000000000 3463753033587 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347322951/10000000000 : ℝ), (2627991647/5000000000 : ℝ), (-2255852989/10000000000 : ℝ)] ![(43564987432807/100000000000000 : ℝ), (21290000213191/50000000000000 : ℝ), (3463753033587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347322951/10000000000 : ℝ)|^519 ≤ (43564987432807/100000000000000 : ℝ)^391
        have hw : |(5347322951/10000000000 : ℝ)|=(5347322951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627991647/5000000000 : ℝ)|^519 ≤ (21290000213191/50000000000000 : ℝ)^391
        have hw : |(2627991647/5000000000 : ℝ)|=(2627991647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2255852989/10000000000 : ℝ)|^519 ≤ (3463753033587/25000000000000 : ℝ)^391
        have hw : |(-2255852989/10000000000 : ℝ)|=(2255852989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s4_3 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2184268837/5000000000 : ℝ)*x 0 + (211260209/500000000 : ℝ)*x 1 + (4516744297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184268837/5000000000 : ℝ)^519 ≤ (33311519684639/100000000000000 : ℝ)^391 := by
    have hnat : (2184268837 : ℕ)^519*100000000000000^391 ≤ 33311519684639^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184268837 5000000000 33311519684639 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211260209/500000000 : ℝ)^519 ≤ (31868605535839/100000000000000 : ℝ)^391 := by
    have hnat : (211260209 : ℕ)^519*100000000000000^391 ≤ 31868605535839^391*500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211260209 500000000 31868605535839 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4516744297/10000000000 : ℝ)^519 ≤ (1392794990289/4000000000000 : ℝ)^391 := by
    have hnat : (4516744297 : ℕ)^519*4000000000000^391 ≤ 1392794990289^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516744297 10000000000 1392794990289 4000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184268837/5000000000 : ℝ), (211260209/500000000 : ℝ), (4516744297/10000000000 : ℝ)] ![(33311519684639/100000000000000 : ℝ), (31868605535839/100000000000000 : ℝ), (1392794990289/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184268837/5000000000 : ℝ)|^519 ≤ (33311519684639/100000000000000 : ℝ)^391
        have hw : |(2184268837/5000000000 : ℝ)|=(2184268837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211260209/500000000 : ℝ)|^519 ≤ (31868605535839/100000000000000 : ℝ)^391
        have hw : |(211260209/500000000 : ℝ)|=(211260209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4516744297/10000000000 : ℝ)|^519 ≤ (1392794990289/4000000000000 : ℝ)^391
        have hw : |(4516744297/10000000000 : ℝ)|=(4516744297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s4_4 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090454813/5000000000 : ℝ)*x 0 + (525640789/1000000000 : ℝ)*x 1 + (5402993899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090454813/5000000000 : ℝ)^519 ≤ (6623694784979/50000000000000 : ℝ)^391 := by
    have hnat : (1090454813 : ℕ)^519*50000000000000^391 ≤ 6623694784979^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090454813 5000000000 6623694784979 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525640789/1000000000 : ℝ)^519 ≤ (21292283150213/50000000000000 : ℝ)^391 := by
    have hnat : (525640789 : ℕ)^519*50000000000000^391 ≤ 21292283150213^391*1000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525640789 1000000000 21292283150213 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402993899/10000000000 : ℝ)^519 ≤ (8833608822179/20000000000000 : ℝ)^391 := by
    have hnat : (5402993899 : ℕ)^519*20000000000000^391 ≤ 8833608822179^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402993899 10000000000 8833608822179 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090454813/5000000000 : ℝ), (525640789/1000000000 : ℝ), (5402993899/10000000000 : ℝ)] ![(6623694784979/50000000000000 : ℝ), (21292283150213/50000000000000 : ℝ), (8833608822179/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090454813/5000000000 : ℝ)|^519 ≤ (6623694784979/50000000000000 : ℝ)^391
        have hw : |(-1090454813/5000000000 : ℝ)|=(1090454813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525640789/1000000000 : ℝ)|^519 ≤ (21292283150213/50000000000000 : ℝ)^391
        have hw : |(525640789/1000000000 : ℝ)|=(525640789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402993899/10000000000 : ℝ)|^519 ≤ (8833608822179/20000000000000 : ℝ)^391
        have hw : |(5402993899/10000000000 : ℝ)|=(5402993899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s4_5 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5310057703/10000000000 : ℝ)*x 0 + (-2108842571/10000000000 : ℝ)*x 1 + (337687131/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310057703/10000000000 : ℝ)^519 ≤ (43162456429/100000000000 : ℝ)^391 := by
    have hnat : (5310057703 : ℕ)^519*100000000000^391 ≤ 43162456429^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310057703 10000000000 43162456429 100000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108842571/10000000000 : ℝ)^519 ≤ (12669497315109/100000000000000 : ℝ)^391 := by
    have hnat : (2108842571 : ℕ)^519*100000000000000^391 ≤ 12669497315109^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108842571 10000000000 12669497315109 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337687131/625000000 : ℝ)^519 ≤ (8833609249703/20000000000000 : ℝ)^391 := by
    have hnat : (337687131 : ℕ)^519*20000000000000^391 ≤ 8833609249703^391*625000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337687131 625000000 8833609249703 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310057703/10000000000 : ℝ), (-2108842571/10000000000 : ℝ), (337687131/625000000 : ℝ)] ![(43162456429/100000000000 : ℝ), (12669497315109/100000000000000 : ℝ), (8833609249703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310057703/10000000000 : ℝ)|^519 ≤ (43162456429/100000000000 : ℝ)^391
        have hw : |(5310057703/10000000000 : ℝ)|=(5310057703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2108842571/10000000000 : ℝ)|^519 ≤ (12669497315109/100000000000000 : ℝ)^391
        have hw : |(-2108842571/10000000000 : ℝ)|=(2108842571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337687131/625000000 : ℝ)|^519 ≤ (8833609249703/20000000000000 : ℝ)^391
        have hw : |(337687131/625000000 : ℝ)|=(337687131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s4_6 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2655029/5000000 : ℝ)*x 0 + (5402994029/10000000000 : ℝ)*x 1 + (-2108842259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655029/5000000 : ℝ)^519 ≤ (43162459633453/100000000000000 : ℝ)^391 := by
    have hnat : (2655029 : ℕ)^519*100000000000000^391 ≤ 43162459633453^391*5000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655029 5000000 43162459633453 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402994029/10000000000 : ℝ)^519 ≤ (44168045521507/100000000000000 : ℝ)^391 := by
    have hnat : (5402994029 : ℕ)^519*100000000000000^391 ≤ 44168045521507^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402994029 10000000000 44168045521507 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108842259/10000000000 : ℝ)^519 ≤ (3167373706763/25000000000000 : ℝ)^391 := by
    have hnat : (2108842259 : ℕ)^519*25000000000000^391 ≤ 3167373706763^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108842259 10000000000 3167373706763 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655029/5000000 : ℝ), (5402994029/10000000000 : ℝ), (-2108842259/10000000000 : ℝ)] ![(43162459633453/100000000000000 : ℝ), (44168045521507/100000000000000 : ℝ), (3167373706763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655029/5000000 : ℝ)|^519 ≤ (43162459633453/100000000000000 : ℝ)^391
        have hw : |(2655029/5000000 : ℝ)|=(2655029/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402994029/10000000000 : ℝ)|^519 ≤ (44168045521507/100000000000000 : ℝ)^391
        have hw : |(5402994029/10000000000 : ℝ)|=(5402994029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108842259/10000000000 : ℝ)|^519 ≤ (3167373706763/25000000000000 : ℝ)^391
        have hw : |(-2108842259/10000000000 : ℝ)|=(2108842259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s4_7 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (436855299/1000000000 : ℝ)*x 0 + (2257952083/5000000000 : ℝ)*x 1 + (132063979/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436855299/1000000000 : ℝ)^519 ≤ (16655837353539/50000000000000 : ℝ)^391 := by
    have hnat : (436855299 : ℕ)^519*50000000000000^391 ≤ 16655837353539^391*1000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436855299 1000000000 16655837353539 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257952083/5000000000 : ℝ)^519 ≤ (34811278169741/100000000000000 : ℝ)^391 := by
    have hnat : (2257952083 : ℕ)^519*100000000000000^391 ≤ 34811278169741^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257952083 5000000000 34811278169741 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132063979/312500000 : ℝ)^519 ≤ (15938523560043/50000000000000 : ℝ)^391 := by
    have hnat : (132063979 : ℕ)^519*50000000000000^391 ≤ 15938523560043^391*312500000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132063979 312500000 15938523560043 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436855299/1000000000 : ℝ), (2257952083/5000000000 : ℝ), (132063979/312500000 : ℝ)] ![(16655837353539/50000000000000 : ℝ), (34811278169741/100000000000000 : ℝ), (15938523560043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436855299/1000000000 : ℝ)|^519 ≤ (16655837353539/50000000000000 : ℝ)^391
        have hw : |(436855299/1000000000 : ℝ)|=(436855299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257952083/5000000000 : ℝ)|^519 ≤ (34811278169741/100000000000000 : ℝ)^391
        have hw : |(2257952083/5000000000 : ℝ)|=(2257952083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132063979/312500000 : ℝ)|^519 ≤ (15938523560043/50000000000000 : ℝ)^391
        have hw : |(132063979/312500000 : ℝ)|=(132063979/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1111_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3711/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2223/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3711/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10541/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3711/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10541/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3711/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10541/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3711/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10541/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3711/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10541/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3711/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10541/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10541/100000 : ℝ) ^ (8303/2048 : ℝ) ≤ (1366086576875009/12500000000000000000 : ℝ) := by
    have hpowers : (10541/100000 : ℝ)^8303 ≤ (1366086576875009/12500000000000000000 : ℝ)^2048 := by
      have hnat : (10541 : ℕ)^8303*12500000000000000000^2048 ≤ 1366086576875009^2048*100000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10541 100000 1366086576875009 12500000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10541/100000 : ℝ)) (X := (1366086576875009/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3711/25000 : ℝ) ^ (8303/2048 : ℝ) ≤ (21891347528798909/50000000000000000000 : ℝ) := by
    have hpowers : (3711/25000 : ℝ)^8303 ≤ (21891347528798909/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3711 : ℕ)^8303*50000000000000000000^2048 ≤ 21891347528798909^2048*25000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3711 25000 21891347528798909 50000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3711/25000 : ℝ)) (X := (21891347528798909/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251366086576875009/6250000000000000000 : ℝ) ≤ (5000269542574899/5000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (6251366086576875009/6250000000000000000 : ℝ)^2048 ≤ (5000269542574899/5000000000000000 : ℝ)^8303 := by
      have hnat : (6251366086576875009 : ℕ)^2048*5000000000000000^8303 ≤ 5000269542574899^8303*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251366086576875009 6250000000000000000 5000269542574899 5000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269542574899/5000000000000000 : ℝ)) (X := (6251366086576875009/6250000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005471138767259789/10000000000000000000 : ℝ) ≤ (5000674610611051/5000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (10005471138767259789/10000000000000000000 : ℝ)^2048 ≤ (5000674610611051/5000000000000000 : ℝ)^8303 := by
      have hnat : (10005471138767259789 : ℕ)^2048*5000000000000000^8303 ≤ 5000674610611051^8303*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005471138767259789 10000000000000000000 5000674610611051 5000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000674610611051/5000000000000000 : ℝ)) (X := (10005471138767259789/10000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25021891347528798909/25000000000000000000 : ℝ) ≤ (5001079678647203/5000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (25021891347528798909/25000000000000000000 : ℝ)^2048 ≤ (5001079678647203/5000000000000000 : ℝ)^8303 := by
      have hnat : (25021891347528798909 : ℕ)^2048*5000000000000000^8303 ≤ 5001079678647203^8303*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021891347528798909 25000000000000000000 5001079678647203 5000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001079678647203/5000000000000000 : ℝ)) (X := (25021891347528798909/25000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1366086576875009/12500000000000000000 : ℝ) ≤ ((1654432322873971841/1655000000000000000 : ℝ)+2*(3894884963/2068750000000 : ℝ)*(10541/100000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (1654432322873971841/1655000000000000000 : ℝ)+2*(3894884963/2068750000000 : ℝ)*(10541/100000 : ℝ)=(5000269542574899/5000000000000000 : ℝ) by norm_num, show 1+2*(1366086576875009/12500000000000000000 : ℝ)=(6251366086576875009/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21891347528798909/50000000000000000000 : ℝ)+(1366086576875009/12500000000000000000 : ℝ) ≤ ((1654432322873971841/1655000000000000000 : ℝ)+(3894884963/2068750000000 : ℝ)*((3711/25000 : ℝ)+(10541/100000 : ℝ)))^(8303/2048 : ℝ) := by
    rw [show (1654432322873971841/1655000000000000000 : ℝ)+(3894884963/2068750000000 : ℝ)*((3711/25000 : ℝ)+(10541/100000 : ℝ))=(5000674610611051/5000000000000000 : ℝ) by norm_num, show 1+(21891347528798909/50000000000000000000 : ℝ)+(1366086576875009/12500000000000000000 : ℝ)=(10005471138767259789/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21891347528798909/50000000000000000000 : ℝ) ≤ ((1654432322873971841/1655000000000000000 : ℝ)+2*(3894884963/2068750000000 : ℝ)*(3711/25000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (1654432322873971841/1655000000000000000 : ℝ)+2*(3894884963/2068750000000 : ℝ)*(3711/25000 : ℝ)=(5001079678647203/5000000000000000 : ℝ) by norm_num, show 1+2*(21891347528798909/50000000000000000000 : ℝ)=(25021891347528798909/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1654432322873971841/1655000000000000000 : ℝ)*(X 1 0+X 2 0)+(3894884963/2068750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (10541/100000 : ℝ)) (hi := (3711/25000 : ℝ)) (c := (1654432322873971841/1655000000000000000 : ℝ)) (alpha := (3894884963/2068750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1654432322873971841/1655000000000000000 : ℝ)*(X 0 1+X 2 1)+(3894884963/2068750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (10541/100000 : ℝ)) (hi := (3711/25000 : ℝ)) (c := (1654432322873971841/1655000000000000000 : ℝ)) (alpha := (3894884963/2068750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1654432322873971841/1655000000000000000 : ℝ)*(X 0 2+X 1 2)+(3894884963/2068750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (10541/100000 : ℝ)) (hi := (3711/25000 : ℝ)) (c := (1654432322873971841/1655000000000000000 : ℝ)) (alpha := (3894884963/2068750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1090451151/5000000000 : ℝ)*X 0 0+(5403420209/10000000000 : ℝ)*X 0 1+(1051196641/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673661581/5000000000 : ℝ)*X 1 0+(-563963127/2500000000 : ℝ)*X 1 1+(2627991723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347322951/10000000000 : ℝ)*X 2 0+(2627991647/5000000000 : ℝ)*X 2 1+(-2255852989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184268837/5000000000 : ℝ)*X 0 0+(211260209/500000000 : ℝ)*X 0 1+(4516744297/10000000000 : ℝ)*X 0 2+(2184268837/5000000000 : ℝ)*X 1 0+(211260209/500000000 : ℝ)*X 1 1+(4516744297/10000000000 : ℝ)*X 1 2+(2184268837/5000000000 : ℝ)*X 2 0+(211260209/500000000 : ℝ)*X 2 1+(4516744297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1090454813/5000000000 : ℝ)*X 0 0+(525640789/1000000000 : ℝ)*X 0 1+(5402993899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310057703/10000000000 : ℝ)*X 1 0+(-2108842571/10000000000 : ℝ)*X 1 1+(337687131/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655029/5000000 : ℝ)*X 2 0+(5402994029/10000000000 : ℝ)*X 2 1+(-2108842259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436855299/1000000000 : ℝ)*X 0 0+(2257952083/5000000000 : ℝ)*X 0 1+(132063979/312500000 : ℝ)*X 0 2+(436855299/1000000000 : ℝ)*X 1 0+(2257952083/5000000000 : ℝ)*X 1 1+(132063979/312500000 : ℝ)*X 1 2+(436855299/1000000000 : ℝ)*X 2 0+(2257952083/5000000000 : ℝ)*X 2 1+(132063979/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (416680915199288702745864033/82750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (390959893/20000000000000 : ℝ)*(base19) + (1929073611/100000000000000 : ℝ)*(base23) + (8131277/6250000000000 : ℝ)*(upper2) + (541126633/100000000000000 : ℝ)*(upper3) + (5106389730414629/100000000000000 : ℝ)*(major0) + (5106389730414629/100000000000000 : ℝ)*(major1) + (5106389730414629/100000000000000 : ℝ)*(major2) + (3391312023122689/50000000000000 : ℝ)*(sp0) + (135653189659697/2000000000000 : ℝ)*(sp1) + (847832413673903/12500000000000 : ℝ)*(sp2) + (1715042518067069/50000000000000 : ℝ)*(sp3) + (37391538937/100000000000000 : ℝ)*(sp4) + (99659741/50000000000000 : ℝ)*(sp6) + (16409531749/50000000000000 : ℝ)*(sp7) + (857529463799409/25000000000000 : ℝ)*(f.failure) + (1695665359446079/25000000000000 : ℝ)*(f.sum) + (973319385019/827500000000000000000000000 : ℝ)*base66 + (144828058162061989/165500000000000000000000000000000 : ℝ)*base67 + (704800660695561989/165500000000000000000000000000000 : ℝ)*base69 + (899130173336061989/165500000000000000000000000000000 : ℝ)*base71 + (566273216777/413750000000000000000000000 : ℝ)*base74 + (844274580682938011/165500000000000000000000000000000 : ℝ)*base76 + (1133636668714061989/165500000000000000000000000000000 : ℝ)*base77 + (2836907309618938011/165500000000000000000000000000000 : ℝ)*base80 + (984105855613/413750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (6909611/2500000000000000000000 : ℝ)*base90 + (6909611/2500000000000000000000 : ℝ)*base92 + (6909611/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214710182646741523448528841/41375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (585024509/100000000000000 : ℝ)*(base19) + (1428719443/100000000000000 : ℝ)*(base23) + (55865917/20000000000000 : ℝ)*(upper3) + (78816727/50000000000000 : ℝ)*(lower4) + (307327369/100000000000000 : ℝ)*(upper5) + (2567978845283111/50000000000000 : ℝ)*(major0) + (2567978845283111/50000000000000 : ℝ)*(major1) + (2567978845283111/50000000000000 : ℝ)*(major2) + (1686934367/20000000000000 : ℝ)*(sp1) + (15992798477/50000000000000 : ℝ)*(sp2) + (1364387130311151/20000000000000 : ℝ)*(sp4) + (6821926631859411/100000000000000 : ℝ)*(sp5) + (3410951118619679/50000000000000 : ℝ)*(sp6) + (3449979556597681/100000000000000 : ℝ)*(sp7) + (3449979556597681/100000000000000 : ℝ)*(f.failure) + (1364387130311151/20000000000000 : ℝ)*(f.sum) + (221408237493/51718750000000000000000000 : ℝ)*base65 + (1180003553432277351/82750000000000000000000000000000 : ℝ)*base67 + (1163003466500527351/82750000000000000000000000000000 : ℝ)*base69 + (1550640356830527351/82750000000000000000000000000000 : ℝ)*base71 + (5655271655401/1655000000000000000000000000 : ℝ)*base73 + (648783205987777351/82750000000000000000000000000000 : ℝ)*base75 + (999151322610277351/82750000000000000000000000000000 : ℝ)*base77 + (335773745295277351/82750000000000000000000000000000 : ℝ)*base79 + (249492332469/413750000000000000000000000 : ℝ)*base81 + (19123499/10000000000000000000000 : ℝ)*base90 + (19123499/10000000000000000000000 : ℝ)*base92 + (19123499/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1111_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3711/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1111_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1111_s5_0 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-136350777/625000000 : ℝ)*x 0 + (5395739397/10000000000 : ℝ)*x 1 + (657899749/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136350777/625000000 : ℝ)^519 ≤ (13253056418497/100000000000000 : ℝ)^391 := by
    have hnat : (136350777 : ℕ)^519*100000000000000^391 ≤ 13253056418497^391*625000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136350777 625000000 13253056418497 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395739397/10000000000 : ℝ)^519 ≤ (5511167975859/12500000000000 : ℝ)^391 := by
    have hnat : (5395739397 : ℕ)^519*12500000000000^391 ≤ 5511167975859^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395739397 10000000000 5511167975859 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657899749/1250000000 : ℝ)^519 ≤ (42657599757789/100000000000000 : ℝ)^391 := by
    have hnat : (657899749 : ℕ)^519*100000000000000^391 ≤ 42657599757789^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657899749 1250000000 42657599757789 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136350777/625000000 : ℝ), (5395739397/10000000000 : ℝ), (657899749/1250000000 : ℝ)] ![(13253056418497/100000000000000 : ℝ), (5511167975859/12500000000000 : ℝ), (42657599757789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136350777/625000000 : ℝ)|^519 ≤ (13253056418497/100000000000000 : ℝ)^391
        have hw : |(-136350777/625000000 : ℝ)|=(136350777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395739397/10000000000 : ℝ)|^519 ≤ (5511167975859/12500000000000 : ℝ)^391
        have hw : |(5395739397/10000000000 : ℝ)|=(5395739397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657899749/1250000000 : ℝ)|^519 ≤ (42657599757789/100000000000000 : ℝ)^391
        have hw : |(657899749/1250000000 : ℝ)|=(657899749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s5_1 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5345401659/10000000000 : ℝ)*x 0 + (-1124439597/5000000000 : ℝ)*x 1 + (5263198093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345401659/10000000000 : ℝ)^519 ≤ (43544211544123/100000000000000 : ℝ)^391 := by
    have hnat : (5345401659 : ℕ)^519*100000000000000^391 ≤ 43544211544123^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345401659 10000000000 43544211544123 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124439597/5000000000 : ℝ)^519 ≤ (13798187594567/100000000000000 : ℝ)^391 := by
    have hnat : (1124439597 : ℕ)^519*100000000000000^391 ≤ 13798187594567^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124439597 5000000000 13798187594567 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263198093/10000000000 : ℝ)^519 ≤ (21328800422181/50000000000000 : ℝ)^391 := by
    have hnat : (5263198093 : ℕ)^519*50000000000000^391 ≤ 21328800422181^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263198093 10000000000 21328800422181 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345401659/10000000000 : ℝ), (-1124439597/5000000000 : ℝ), (5263198093/10000000000 : ℝ)] ![(43544211544123/100000000000000 : ℝ), (13798187594567/100000000000000 : ℝ), (21328800422181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345401659/10000000000 : ℝ)|^519 ≤ (43544211544123/100000000000000 : ℝ)^391
        have hw : |(5345401659/10000000000 : ℝ)|=(5345401659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1124439597/5000000000 : ℝ)|^519 ≤ (13798187594567/100000000000000 : ℝ)^391
        have hw : |(-1124439597/5000000000 : ℝ)|=(1124439597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263198093/10000000000 : ℝ)|^519 ≤ (21328800422181/50000000000000 : ℝ)^391
        have hw : |(5263198093/10000000000 : ℝ)|=(5263198093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s5_2 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1336350431/2500000000 : ℝ)*x 0 + (2631599013/5000000000 : ℝ)*x 1 + (-2248879197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336350431/2500000000 : ℝ)^519 ≤ (544302653087/1250000000000 : ℝ)^391 := by
    have hnat : (1336350431 : ℕ)^519*1250000000000^391 ≤ 544302653087^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336350431 2500000000 544302653087 1250000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631599013/5000000000 : ℝ)^519 ≤ (21328800061783/50000000000000 : ℝ)^391 := by
    have hnat : (2631599013 : ℕ)^519*50000000000000^391 ≤ 21328800061783^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631599013 5000000000 21328800061783 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248879197/10000000000 : ℝ)^519 ≤ (13798187618999/100000000000000 : ℝ)^391 := by
    have hnat : (2248879197 : ℕ)^519*100000000000000^391 ≤ 13798187618999^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248879197 10000000000 13798187618999 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336350431/2500000000 : ℝ), (2631599013/5000000000 : ℝ), (-2248879197/10000000000 : ℝ)] ![(544302653087/1250000000000 : ℝ), (21328800061783/50000000000000 : ℝ), (13798187618999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336350431/2500000000 : ℝ)|^519 ≤ (544302653087/1250000000000 : ℝ)^391
        have hw : |(1336350431/2500000000 : ℝ)|=(1336350431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631599013/5000000000 : ℝ)|^519 ≤ (21328800061783/50000000000000 : ℝ)^391
        have hw : |(2631599013/5000000000 : ℝ)|=(2631599013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2248879197/10000000000 : ℝ)|^519 ≤ (13798187618999/100000000000000 : ℝ)^391
        have hw : |(-2248879197/10000000000 : ℝ)|=(2248879197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s5_3 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2184475369/5000000000 : ℝ)*x 0 + (4239877843/10000000000 : ℝ)*x 1 + (562745377/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184475369/5000000000 : ℝ)^519 ≤ (33315700615911/100000000000000 : ℝ)^391 := by
    have hnat : (2184475369 : ℕ)^519*100000000000000^391 ≤ 33315700615911^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184475369 5000000000 33315700615911 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239877843/10000000000 : ℝ)^519 ≤ (6403119332231/20000000000000 : ℝ)^391 := by
    have hnat : (4239877843 : ℕ)^519*20000000000000^391 ≤ 6403119332231^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239877843 10000000000 6403119332231 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562745377/1250000000 : ℝ)^519 ≤ (8667175676527/25000000000000 : ℝ)^391 := by
    have hnat : (562745377 : ℕ)^519*25000000000000^391 ≤ 8667175676527^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562745377 1250000000 8667175676527 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184475369/5000000000 : ℝ), (4239877843/10000000000 : ℝ), (562745377/1250000000 : ℝ)] ![(33315700615911/100000000000000 : ℝ), (6403119332231/20000000000000 : ℝ), (8667175676527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184475369/5000000000 : ℝ)|^519 ≤ (33315700615911/100000000000000 : ℝ)^391
        have hw : |(2184475369/5000000000 : ℝ)|=(2184475369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239877843/10000000000 : ℝ)|^519 ≤ (6403119332231/20000000000000 : ℝ)^391
        have hw : |(4239877843/10000000000 : ℝ)|=(4239877843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562745377/1250000000 : ℝ)|^519 ≤ (8667175676527/25000000000000 : ℝ)^391
        have hw : |(562745377/1250000000 : ℝ)|=(562745377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s5_4 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090808677/5000000000 : ℝ)*x 0 + (5263541729/10000000000 : ℝ)*x 1 + (5395394781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090808677/5000000000 : ℝ)^519 ≤ (6626548053779/50000000000000 : ℝ)^391 := by
    have hnat : (1090808677 : ℕ)^519*50000000000000^391 ≤ 6626548053779^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090808677 5000000000 6626548053779 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263541729/10000000000 : ℝ)^519 ≤ (42661297769079/100000000000000 : ℝ)^391 := by
    have hnat : (5263541729 : ℕ)^519*100000000000000^391 ≤ 42661297769079^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263541729 10000000000 42661297769079 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395394781/10000000000 : ℝ)^519 ≤ (4408560610923/10000000000000 : ℝ)^391 := by
    have hnat : (5395394781 : ℕ)^519*10000000000000^391 ≤ 4408560610923^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395394781 10000000000 4408560610923 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090808677/5000000000 : ℝ), (5263541729/10000000000 : ℝ), (5395394781/10000000000 : ℝ)] ![(6626548053779/50000000000000 : ℝ), (42661297769079/100000000000000 : ℝ), (4408560610923/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090808677/5000000000 : ℝ)|^519 ≤ (6626548053779/50000000000000 : ℝ)^391
        have hw : |(-1090808677/5000000000 : ℝ)|=(1090808677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263541729/10000000000 : ℝ)|^519 ≤ (42661297769079/100000000000000 : ℝ)^391
        have hw : |(5263541729/10000000000 : ℝ)|=(5263541729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395394781/10000000000 : ℝ)|^519 ≤ (4408560610923/10000000000000 : ℝ)^391
        have hw : |(5395394781/10000000000 : ℝ)|=(5395394781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s5_5 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (106238009/200000000 : ℝ)*x 0 + (-2116682861/10000000000 : ℝ)*x 1 + (2697697211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106238009/200000000 : ℝ)^519 ≤ (4318233970277/10000000000000 : ℝ)^391 := by
    have hnat : (106238009 : ℕ)^519*10000000000000^391 ≤ 4318233970277^391*200000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106238009 200000000 4318233970277 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116682861/10000000000 : ℝ)^519 ≤ (3183014515957/25000000000000 : ℝ)^391 := by
    have hnat : (2116682861 : ℕ)^519*25000000000000^391 ≤ 3183014515957^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116682861 10000000000 3183014515957 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697697211/5000000000 : ℝ)^519 ≤ (8817120443113/20000000000000 : ℝ)^391 := by
    have hnat : (2697697211 : ℕ)^519*20000000000000^391 ≤ 8817120443113^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697697211 5000000000 8817120443113 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106238009/200000000 : ℝ), (-2116682861/10000000000 : ℝ), (2697697211/5000000000 : ℝ)] ![(4318233970277/10000000000000 : ℝ), (3183014515957/25000000000000 : ℝ), (8817120443113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106238009/200000000 : ℝ)|^519 ≤ (4318233970277/10000000000000 : ℝ)^391
        have hw : |(106238009/200000000 : ℝ)|=(106238009/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2116682861/10000000000 : ℝ)|^519 ≤ (3183014515957/25000000000000 : ℝ)^391
        have hw : |(-2116682861/10000000000 : ℝ)|=(2116682861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697697211/5000000000 : ℝ)|^519 ≤ (8817120443113/20000000000000 : ℝ)^391
        have hw : |(2697697211/5000000000 : ℝ)|=(2697697211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s5_6 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5311900549/10000000000 : ℝ)*x 0 + (215815789/400000000 : ℝ)*x 1 + (-423336463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311900549/10000000000 : ℝ)^519 ≤ (21591170385521/50000000000000 : ℝ)^391 := by
    have hnat : (5311900549 : ℕ)^519*50000000000000^391 ≤ 21591170385521^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311900549 10000000000 21591170385521 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215815789/400000000 : ℝ)^519 ≤ (22042802750931/50000000000000 : ℝ)^391 := by
    have hnat : (215815789 : ℕ)^519*50000000000000^391 ≤ 22042802750931^391*400000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215815789 400000000 22042802750931 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423336463/2000000000 : ℝ)^519 ≤ (2546410740887/20000000000000 : ℝ)^391 := by
    have hnat : (423336463 : ℕ)^519*20000000000000^391 ≤ 2546410740887^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423336463 2000000000 2546410740887 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311900549/10000000000 : ℝ), (215815789/400000000 : ℝ), (-423336463/2000000000 : ℝ)] ![(21591170385521/50000000000000 : ℝ), (22042802750931/50000000000000 : ℝ), (2546410740887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311900549/10000000000 : ℝ)|^519 ≤ (21591170385521/50000000000000 : ℝ)^391
        have hw : |(5311900549/10000000000 : ℝ)|=(5311900549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215815789/400000000 : ℝ)|^519 ≤ (22042802750931/50000000000000 : ℝ)^391
        have hw : |(215815789/400000000 : ℝ)|=(215815789/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423336463/2000000000 : ℝ)|^519 ≤ (2546410740887/20000000000000 : ℝ)^391
        have hw : |(-423336463/2000000000 : ℝ)|=(423336463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s5_7 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2184480887/5000000000 : ℝ)*x 0 + (2250641993/5000000000 : ℝ)*x 1 + (4240559157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184480887/5000000000 : ℝ)^519 ≤ (33315812321339/100000000000000 : ℝ)^391 := by
    have hnat : (2184480887 : ℕ)^519*100000000000000^391 ≤ 33315812321339^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184480887 5000000000 33315812321339 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250641993/5000000000 : ℝ)^519 ≤ (17330880993187/50000000000000 : ℝ)^391 := by
    have hnat : (2250641993 : ℕ)^519*50000000000000^391 ≤ 17330880993187^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250641993 5000000000 17330880993187 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240559157/10000000000 : ℝ)^519 ≤ (3202242566869/10000000000000 : ℝ)^391 := by
    have hnat : (4240559157 : ℕ)^519*10000000000000^391 ≤ 3202242566869^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240559157 10000000000 3202242566869 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184480887/5000000000 : ℝ), (2250641993/5000000000 : ℝ), (4240559157/10000000000 : ℝ)] ![(33315812321339/100000000000000 : ℝ), (17330880993187/50000000000000 : ℝ), (3202242566869/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184480887/5000000000 : ℝ)|^519 ≤ (33315812321339/100000000000000 : ℝ)^391
        have hw : |(2184480887/5000000000 : ℝ)|=(2184480887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250641993/5000000000 : ℝ)|^519 ≤ (17330880993187/50000000000000 : ℝ)^391
        have hw : |(2250641993/5000000000 : ℝ)|=(2250641993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240559157/10000000000 : ℝ)|^519 ≤ (3202242566869/10000000000000 : ℝ)^391
        have hw : |(4240559157/10000000000 : ℝ)|=(4240559157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1111_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3519/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2223/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2223/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2223/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2223/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2223/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2223/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2223/20000 : ℝ) ^ (8303/2048 : ℝ) ≤ (3387403370415359/25000000000000000000 : ℝ) := by
    have hpowers : (2223/20000 : ℝ)^8303 ≤ (3387403370415359/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2223 : ℕ)^8303*25000000000000000000^2048 ≤ 3387403370415359^2048*20000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2223 20000 3387403370415359 25000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2223/20000 : ℝ)) (X := (3387403370415359/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8303/2048 : ℝ) ≤ (36964929601245961/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8303 ≤ (36964929601245961/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8303*100000000000000000000^2048 ≤ 36964929601245961^2048*100000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 36964929601245961 100000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (36964929601245961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503387403370415359/12500000000000000000 : ℝ) ≤ (10000668355445479/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (12503387403370415359/12500000000000000000 : ℝ)^2048 ≤ (10000668355445479/10000000000000000 : ℝ)^8303 := by
      have hnat : (12503387403370415359 : ℕ)^2048*10000000000000000^8303 ≤ 10000668355445479^8303*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503387403370415359 12500000000000000000 10000668355445479 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000668355445479/10000000000000000 : ℝ)) (X := (12503387403370415359/12500000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050514543082907397/100000000000000000000 : ℝ) ≤ (10001245743773473/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (100050514543082907397/100000000000000000000 : ℝ)^2048 ≤ (10001245743773473/10000000000000000 : ℝ)^8303 := by
      have hnat : (100050514543082907397 : ℕ)^2048*10000000000000000^8303 ≤ 10001245743773473^8303*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050514543082907397 100000000000000000000 10001245743773473 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001245743773473/10000000000000000 : ℝ)) (X := (100050514543082907397/100000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036964929601245961/50000000000000000000 : ℝ) ≤ (10001823132101467/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (50036964929601245961/50000000000000000000 : ℝ)^2048 ≤ (10001823132101467/10000000000000000 : ℝ)^8303 := by
      have hnat : (50036964929601245961 : ℕ)^2048*10000000000000000^8303 ≤ 10001823132101467^8303*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036964929601245961 50000000000000000000 10001823132101467 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001823132101467/10000000000000000 : ℝ)) (X := (50036964929601245961/50000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3387403370415359/25000000000000000000 : ℝ) ≤ ((15604625631584739409/15610000000000000000 : ℝ)+2*(288694163997/156100000000000 : ℝ)*(2223/20000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (15604625631584739409/15610000000000000000 : ℝ)+2*(288694163997/156100000000000 : ℝ)*(2223/20000 : ℝ)=(10000668355445479/10000000000000000 : ℝ) by norm_num, show 1+2*(3387403370415359/25000000000000000000 : ℝ)=(12503387403370415359/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36964929601245961/100000000000000000000 : ℝ)+(3387403370415359/25000000000000000000 : ℝ) ≤ ((15604625631584739409/15610000000000000000 : ℝ)+(288694163997/156100000000000 : ℝ)*((14237/100000 : ℝ)+(2223/20000 : ℝ)))^(8303/2048 : ℝ) := by
    rw [show (15604625631584739409/15610000000000000000 : ℝ)+(288694163997/156100000000000 : ℝ)*((14237/100000 : ℝ)+(2223/20000 : ℝ))=(10001245743773473/10000000000000000 : ℝ) by norm_num, show 1+(36964929601245961/100000000000000000000 : ℝ)+(3387403370415359/25000000000000000000 : ℝ)=(100050514543082907397/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36964929601245961/100000000000000000000 : ℝ) ≤ ((15604625631584739409/15610000000000000000 : ℝ)+2*(288694163997/156100000000000 : ℝ)*(14237/100000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (15604625631584739409/15610000000000000000 : ℝ)+2*(288694163997/156100000000000 : ℝ)*(14237/100000 : ℝ)=(10001823132101467/10000000000000000 : ℝ) by norm_num, show 1+2*(36964929601245961/100000000000000000000 : ℝ)=(50036964929601245961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15604625631584739409/15610000000000000000 : ℝ)*(X 1 0+X 2 0)+(288694163997/156100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (15604625631584739409/15610000000000000000 : ℝ)) (alpha := (288694163997/156100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15604625631584739409/15610000000000000000 : ℝ)*(X 0 1+X 2 1)+(288694163997/156100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (15604625631584739409/15610000000000000000 : ℝ)) (alpha := (288694163997/156100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15604625631584739409/15610000000000000000 : ℝ)*(X 0 2+X 1 2)+(288694163997/156100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (15604625631584739409/15610000000000000000 : ℝ)) (alpha := (288694163997/156100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-136350777/625000000 : ℝ)*X 0 0+(5395739397/10000000000 : ℝ)*X 0 1+(657899749/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345401659/10000000000 : ℝ)*X 1 0+(-1124439597/5000000000 : ℝ)*X 1 1+(5263198093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336350431/2500000000 : ℝ)*X 2 0+(2631599013/5000000000 : ℝ)*X 2 1+(-2248879197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184475369/5000000000 : ℝ)*X 0 0+(4239877843/10000000000 : ℝ)*X 0 1+(562745377/1250000000 : ℝ)*X 0 2+(2184475369/5000000000 : ℝ)*X 1 0+(4239877843/10000000000 : ℝ)*X 1 1+(562745377/1250000000 : ℝ)*X 1 2+(2184475369/5000000000 : ℝ)*X 2 0+(4239877843/10000000000 : ℝ)*X 2 1+(562745377/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1090808677/5000000000 : ℝ)*X 0 0+(5263541729/10000000000 : ℝ)*X 0 1+(5395394781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106238009/200000000 : ℝ)*X 1 0+(-2116682861/10000000000 : ℝ)*X 1 1+(2697697211/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311900549/10000000000 : ℝ)*X 2 0+(215815789/400000000 : ℝ)*X 2 1+(-423336463/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184480887/5000000000 : ℝ)*X 0 0+(2250641993/5000000000 : ℝ)*X 0 1+(4240559157/10000000000 : ℝ)*X 0 2+(2184480887/5000000000 : ℝ)*X 1 0+(2250641993/5000000000 : ℝ)*X 1 1+(4240559157/10000000000 : ℝ)*X 1 2+(2184480887/5000000000 : ℝ)*X 2 0+(2250641993/5000000000 : ℝ)*X 2 1+(4240559157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101484239047243736346746889/19512500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106998129/10000000000000 : ℝ)*(base19) + (215568819/20000000000000 : ℝ)*(base23) + (44838719/100000000000000 : ℝ)*(lower2) + (1787451/1250000000000 : ℝ)*(upper3) + (93630251/100000000000000 : ℝ)*(upper5) + (142005802220907/2500000000000 : ℝ)*(major0) + (142005802220907/2500000000000 : ℝ)*(major1) + (142005802220907/2500000000000 : ℝ)*(major2) + (7544845433890019/100000000000000 : ℝ)*(sp0) + (37724388251777/500000000000 : ℝ)*(sp1) + (1508975528498519/20000000000000 : ℝ)*(sp2) + (476946052189279/12500000000000 : ℝ)*(sp3) + (33286446671/100000000000000 : ℝ)*(sp4) + (8433227717/50000000000000 : ℝ)*(sp7) + (1907792641984833/50000000000000 : ℝ)*(f.failure) + (754487872033669/10000000000000 : ℝ)*(f.sum) + (4496763277721/780500000000000000000000000 : ℝ)*base65 + (31717674736932291/5575000000000000000000000000000 : ℝ)*base68 + (6683497086457291/5575000000000000000000000000000 : ℝ)*base70 + (15091488533317709/5575000000000000000000000000000 : ℝ)*base71 + (198376726083/390250000000000000000000000 : ℝ)*base73 + (1375799285467709/5575000000000000000000000000000 : ℝ)*base75 + (17637246845182291/5575000000000000000000000000000 : ℝ)*base78 + (44532396318532291/5575000000000000000000000000000 : ℝ)*base80 + (10801624997/1561000000000000000000000000 : ℝ)*base81 + (17474907/5000000000000000000000 : ℝ)*base90 + (17474907/5000000000000000000000 : ℝ)*base92 + (17474907/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140070012647443948307439813/24390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36956607/6250000000000 : ℝ)*(base19) + (176955309/25000000000000 : ℝ)*(base23) + (82553029/25000000000000 : ℝ)*(lower2) + (54619759/25000000000000 : ℝ)*(lower4) + (9689723/20000000000000 : ℝ)*(lower5) + (178432475571981/3125000000000 : ℝ)*(major0) + (178432475571981/3125000000000 : ℝ)*(major1) + (178432475571981/3125000000000 : ℝ)*(major2) + (1470714727/5000000000000 : ℝ)*(sp2) + (817038171/20000000000000 : ℝ)*(sp3) + (1516840989717231/20000000000000 : ℝ)*(sp4) + (7584204357280443/100000000000000 : ℝ)*(sp5) + (379208741323519/5000000000000 : ℝ)*(sp6) + (191773460570187/5000000000000 : ℝ)*(sp7) + (1917736648297297/50000000000000 : ℝ)*(f.failure) + (1516840989717231/20000000000000 : ℝ)*(f.sum) + (5923700411947/975625000000000000000000000 : ℝ)*base66 + (40525726865192747/6968750000000000000000000000000 : ℝ)*base67 + (28097466370036497/6968750000000000000000000000000 : ℝ)*base69 + (59825943544182253/6968750000000000000000000000000 : ℝ)*base72 + (13794331255843/3902500000000000000000000000 : ℝ)*base74 + (5546369129630247/6968750000000000000000000000000 : ℝ)*base75 + (12188239290505247/6968750000000000000000000000000 : ℝ)*base77 + (108167617651526003/6968750000000000000000000000000 : ℝ)*base80 + (4211866691269/1951250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (19204363/5000000000000000000000 : ℝ)*base90 + (19204363/5000000000000000000000 : ℝ)*base92 + (19204363/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1111_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1111_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1111_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16597/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1111_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1111_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1111_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16597/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1111_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

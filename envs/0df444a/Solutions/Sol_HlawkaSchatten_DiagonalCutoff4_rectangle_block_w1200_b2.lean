-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1200_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:03:04.194163+00:00
-- url     : https://prove2.me/submissions/4a82a148-3cf2-4063-9873-93e02eecae52

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
theorem support_rectangle_w1200_s6_0 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139432717/10000000000 : ℝ)*x 0 + (5392227601/10000000000 : ℝ)*x 1 + (2633195551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139432717/10000000000 : ℝ)^8393 ≤ (6502892233499/50000000000000 : ℝ)^6345 := by
    have hnat : (2139432717 : ℕ)^8393*50000000000000^6345 ≤ 6502892233499^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139432717 10000000000 6502892233499 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392227601/10000000000 : ℝ)^8393 ≤ (44176368548959/100000000000000 : ℝ)^6345 := by
    have hnat : (5392227601 : ℕ)^8393*100000000000000^6345 ≤ 44176368548959^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392227601 10000000000 44176368548959 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633195551/5000000000 : ℝ)^8393 ≤ (2676115434787/6250000000000 : ℝ)^6345 := by
    have hnat : (2633195551 : ℕ)^8393*6250000000000^6345 ≤ 2676115434787^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633195551 5000000000 2676115434787 6250000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139432717/10000000000 : ℝ), (5392227601/10000000000 : ℝ), (2633195551/5000000000 : ℝ)] ![(6502892233499/50000000000000 : ℝ), (44176368548959/100000000000000 : ℝ), (2676115434787/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139432717/10000000000 : ℝ)|^8393 ≤ (6502892233499/50000000000000 : ℝ)^6345
        have hw : |(-2139432717/10000000000 : ℝ)|=(2139432717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392227601/10000000000 : ℝ)|^8393 ≤ (44176368548959/100000000000000 : ℝ)^6345
        have hw : |(5392227601/10000000000 : ℝ)|=(5392227601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633195551/5000000000 : ℝ)|^8393 ≤ (2676115434787/6250000000000 : ℝ)^6345
        have hw : |(2633195551/5000000000 : ℝ)|=(2633195551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s6_1 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672290207/5000000000 : ℝ)*x 0 + (-2203248493/10000000000 : ℝ)*x 1 + (2633195567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672290207/5000000000 : ℝ)^8393 ≤ (43660755800471/100000000000000 : ℝ)^6345 := by
    have hnat : (2672290207 : ℕ)^8393*100000000000000^6345 ≤ 43660755800471^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672290207 5000000000 43660755800471 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203248493/10000000000 : ℝ)^8393 ≤ (1352139688781/10000000000000 : ℝ)^6345 := by
    have hnat : (2203248493 : ℕ)^8393*10000000000000^6345 ≤ 1352139688781^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203248493 10000000000 1352139688781 10000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633195567/5000000000 : ℝ)^8393 ≤ (21408923650371/50000000000000 : ℝ)^6345 := by
    have hnat : (2633195567 : ℕ)^8393*50000000000000^6345 ≤ 21408923650371^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633195567 5000000000 21408923650371 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672290207/5000000000 : ℝ), (-2203248493/10000000000 : ℝ), (2633195567/5000000000 : ℝ)] ![(43660755800471/100000000000000 : ℝ), (1352139688781/10000000000000 : ℝ), (21408923650371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672290207/5000000000 : ℝ)|^8393 ≤ (43660755800471/100000000000000 : ℝ)^6345
        have hw : |(2672290207/5000000000 : ℝ)|=(2672290207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2203248493/10000000000 : ℝ)|^8393 ≤ (1352139688781/10000000000000 : ℝ)^6345
        have hw : |(-2203248493/10000000000 : ℝ)|=(2203248493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633195567/5000000000 : ℝ)|^8393 ≤ (21408923650371/50000000000000 : ℝ)^6345
        have hw : |(2633195567/5000000000 : ℝ)|=(2633195567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s6_2 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344580467/10000000000 : ℝ)*x 0 + (2633195519/5000000000 : ℝ)*x 1 + (-2203248549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344580467/10000000000 : ℝ)^8393 ≤ (43660756373187/100000000000000 : ℝ)^6345 := by
    have hnat : (5344580467 : ℕ)^8393*100000000000000^6345 ≤ 43660756373187^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344580467 10000000000 43660756373187 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633195519/5000000000 : ℝ)^8393 ≤ (42817846268293/100000000000000 : ℝ)^6345 := by
    have hnat : (2633195519 : ℕ)^8393*100000000000000^6345 ≤ 42817846268293^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633195519 5000000000 42817846268293 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203248549/10000000000 : ℝ)^8393 ≤ (3380349335603/25000000000000 : ℝ)^6345 := by
    have hnat : (2203248549 : ℕ)^8393*25000000000000^6345 ≤ 3380349335603^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203248549 10000000000 3380349335603 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344580467/10000000000 : ℝ), (2633195519/5000000000 : ℝ), (-2203248549/10000000000 : ℝ)] ![(43660756373187/100000000000000 : ℝ), (42817846268293/100000000000000 : ℝ), (3380349335603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344580467/10000000000 : ℝ)|^8393 ≤ (43660756373187/100000000000000 : ℝ)^6345
        have hw : |(5344580467/10000000000 : ℝ)|=(5344580467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633195519/5000000000 : ℝ)|^8393 ≤ (42817846268293/100000000000000 : ℝ)^6345
        have hw : |(2633195519/5000000000 : ℝ)|=(2633195519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2203248549/10000000000 : ℝ)|^8393 ≤ (3380349335603/25000000000000 : ℝ)^6345
        have hw : |(-2203248549/10000000000 : ℝ)|=(2203248549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s6_3 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356553451/10000000000 : ℝ)*x 0 + (4231759179/10000000000 : ℝ)*x 1 + (35879673/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356553451/10000000000 : ℝ)^8393 ≤ (8329287865663/25000000000000 : ℝ)^6345 := by
    have hnat : (4356553451 : ℕ)^8393*25000000000000^6345 ≤ 8329287865663^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356553451 10000000000 8329287865663 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231759179/10000000000 : ℝ)^8393 ≤ (32060602308149/100000000000000 : ℝ)^6345 := by
    have hnat : (4231759179 : ℕ)^8393*100000000000000^6345 ≤ 32060602308149^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231759179 10000000000 32060602308149 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35879673/80000000 : ℝ)^8393 ≤ (2163890388289/6250000000000 : ℝ)^6345 := by
    have hnat : (35879673 : ℕ)^8393*6250000000000^6345 ≤ 2163890388289^6345*80000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35879673 80000000 2163890388289 6250000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356553451/10000000000 : ℝ), (4231759179/10000000000 : ℝ), (35879673/80000000 : ℝ)] ![(8329287865663/25000000000000 : ℝ), (32060602308149/100000000000000 : ℝ), (2163890388289/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356553451/10000000000 : ℝ)|^8393 ≤ (8329287865663/25000000000000 : ℝ)^6345
        have hw : |(4356553451/10000000000 : ℝ)|=(4356553451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231759179/10000000000 : ℝ)|^8393 ≤ (32060602308149/100000000000000 : ℝ)^6345
        have hw : |(4231759179/10000000000 : ℝ)|=(4231759179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35879673/80000000 : ℝ)|^8393 ≤ (2163890388289/6250000000000 : ℝ)^6345
        have hw : |(35879673/80000000 : ℝ)|=(35879673/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s6_4 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-534859371/2500000000 : ℝ)*x 0 + (1316677269/2500000000 : ℝ)*x 1 + (5391908499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534859371/2500000000 : ℝ)^8393 ≤ (6502911399823/50000000000000 : ℝ)^6345 := by
    have hnat : (534859371 : ℕ)^8393*50000000000000^6345 ≤ 6502911399823^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534859371 2500000000 6502911399823 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316677269/2500000000 : ℝ)^8393 ≤ (10705316674281/25000000000000 : ℝ)^6345 := by
    have hnat : (1316677269 : ℕ)^8393*25000000000000^6345 ≤ 10705316674281^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316677269 2500000000 10705316674281 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391908499/10000000000 : ℝ)^8393 ≤ (44172910486983/100000000000000 : ℝ)^6345 := by
    have hnat : (5391908499 : ℕ)^8393*100000000000000^6345 ≤ 44172910486983^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391908499 10000000000 44172910486983 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534859371/2500000000 : ℝ), (1316677269/2500000000 : ℝ), (5391908499/10000000000 : ℝ)] ![(6502911399823/50000000000000 : ℝ), (10705316674281/25000000000000 : ℝ), (44172910486983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534859371/2500000000 : ℝ)|^8393 ≤ (6502911399823/50000000000000 : ℝ)^6345
        have hw : |(-534859371/2500000000 : ℝ)|=(534859371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316677269/2500000000 : ℝ)|^8393 ≤ (10705316674281/25000000000000 : ℝ)^6345
        have hw : |(1316677269/2500000000 : ℝ)|=(1316677269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391908499/10000000000 : ℝ)|^8393 ≤ (44172910486983/100000000000000 : ℝ)^6345
        have hw : |(5391908499/10000000000 : ℝ)|=(5391908499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s6_5 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312565511/10000000000 : ℝ)*x 0 + (-2077731223/10000000000 : ℝ)*x 1 + (1347977091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312565511/10000000000 : ℝ)^8393 ≤ (5414392379453/12500000000000 : ℝ)^6345 := by
    have hnat : (5312565511 : ℕ)^8393*12500000000000^6345 ≤ 5414392379453^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312565511 10000000000 5414392379453 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077731223/10000000000 : ℝ)^8393 ≤ (6255975962533/50000000000000 : ℝ)^6345 := by
    have hnat : (2077731223 : ℕ)^8393*50000000000000^6345 ≤ 6255975962533^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077731223 10000000000 6255975962533 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347977091/2500000000 : ℝ)^8393 ≤ (22086454512011/50000000000000 : ℝ)^6345 := by
    have hnat : (1347977091 : ℕ)^8393*50000000000000^6345 ≤ 22086454512011^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347977091 2500000000 22086454512011 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312565511/10000000000 : ℝ), (-2077731223/10000000000 : ℝ), (1347977091/2500000000 : ℝ)] ![(5414392379453/12500000000000 : ℝ), (6255975962533/50000000000000 : ℝ), (22086454512011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312565511/10000000000 : ℝ)|^8393 ≤ (5414392379453/12500000000000 : ℝ)^6345
        have hw : |(5312565511/10000000000 : ℝ)|=(5312565511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077731223/10000000000 : ℝ)|^8393 ≤ (6255975962533/50000000000000 : ℝ)^6345
        have hw : |(-2077731223/10000000000 : ℝ)|=(2077731223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347977091/2500000000 : ℝ)|^8393 ≤ (22086454512011/50000000000000 : ℝ)^6345
        have hw : |(1347977091/2500000000 : ℝ)|=(1347977091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s6_6 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656282779/5000000000 : ℝ)*x 0 + (2695954173/5000000000 : ℝ)*x 1 + (-129858199/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656282779/5000000000 : ℝ)^8393 ≤ (1082878488563/2500000000000 : ℝ)^6345 := by
    have hnat : (2656282779 : ℕ)^8393*2500000000000^6345 ≤ 1082878488563^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656282779 5000000000 1082878488563 2500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695954173/5000000000 : ℝ)^8393 ≤ (276080680181/625000000000 : ℝ)^6345 := by
    have hnat : (2695954173 : ℕ)^8393*625000000000^6345 ≤ 276080680181^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695954173 5000000000 276080680181 625000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129858199/625000000 : ℝ)^8393 ≤ (2502390322881/20000000000000 : ℝ)^6345 := by
    have hnat : (129858199 : ℕ)^8393*20000000000000^6345 ≤ 2502390322881^6345*625000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129858199 625000000 2502390322881 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656282779/5000000000 : ℝ), (2695954173/5000000000 : ℝ), (-129858199/625000000 : ℝ)] ![(1082878488563/2500000000000 : ℝ), (276080680181/625000000000 : ℝ), (2502390322881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656282779/5000000000 : ℝ)|^8393 ≤ (1082878488563/2500000000000 : ℝ)^6345
        have hw : |(2656282779/5000000000 : ℝ)|=(2656282779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695954173/5000000000 : ℝ)|^8393 ≤ (276080680181/625000000000 : ℝ)^6345
        have hw : |(2695954173/5000000000 : ℝ)|=(2695954173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129858199/625000000 : ℝ)|^8393 ≤ (2502390322881/20000000000000 : ℝ)^6345
        have hw : |(-129858199/625000000 : ℝ)|=(129858199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s6_7 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089140731/2500000000 : ℝ)*x 0 + (4484319257/10000000000 : ℝ)*x 1 + (4232401569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089140731/2500000000 : ℝ)^8393 ≤ (6663449458381/20000000000000 : ℝ)^6345 := by
    have hnat : (1089140731 : ℕ)^8393*20000000000000^6345 ≤ 6663449458381^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089140731 2500000000 6663449458381 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484319257/10000000000 : ℝ)^8393 ≤ (17307856229611/50000000000000 : ℝ)^6345 := by
    have hnat : (4484319257 : ℕ)^8393*50000000000000^6345 ≤ 17307856229611^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484319257 10000000000 17307856229611 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232401569/10000000000 : ℝ)^8393 ≤ (32067040230581/100000000000000 : ℝ)^6345 := by
    have hnat : (4232401569 : ℕ)^8393*100000000000000^6345 ≤ 32067040230581^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232401569 10000000000 32067040230581 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089140731/2500000000 : ℝ), (4484319257/10000000000 : ℝ), (4232401569/10000000000 : ℝ)] ![(6663449458381/20000000000000 : ℝ), (17307856229611/50000000000000 : ℝ), (32067040230581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089140731/2500000000 : ℝ)|^8393 ≤ (6663449458381/20000000000000 : ℝ)^6345
        have hw : |(1089140731/2500000000 : ℝ)|=(1089140731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484319257/10000000000 : ℝ)|^8393 ≤ (17307856229611/50000000000000 : ℝ)^6345
        have hw : |(4484319257/10000000000 : ℝ)|=(4484319257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232401569/10000000000 : ℝ)|^8393 ≤ (32067040230581/100000000000000 : ℝ)^6345
        have hw : |(4232401569/10000000000 : ℝ)|=(4232401569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1200_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5711/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14087/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11397/100000 : ℝ) ^ (1049/256 : ℝ) ≤ (545898481693829/4000000000000000000 : ℝ) := by
    have hpowers : (11397/100000 : ℝ)^1049 ≤ (545898481693829/4000000000000000000 : ℝ)^256 := by
      have hnat : (11397 : ℕ)^1049*4000000000000000000^256 ≤ 545898481693829^256*100000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11397 100000 545898481693829 4000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11397/100000 : ℝ)) (X := (545898481693829/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14113/100000 : ℝ) ^ (1049/256 : ℝ) ≤ (4095834435268471/12500000000000000000 : ℝ) := by
    have hpowers : (14113/100000 : ℝ)^1049 ≤ (4095834435268471/12500000000000000000 : ℝ)^256 := by
      have hnat : (14113 : ℕ)^1049*12500000000000000000^256 ≤ 4095834435268471^256*100000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14113 100000 4095834435268471 12500000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14113/100000 : ℝ)) (X := (4095834435268471/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000545898481693829/2000000000000000000 : ℝ) ≤ (5000333020962191/5000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (2000545898481693829/2000000000000000000 : ℝ)^256 ≤ (5000333020962191/5000000000000000 : ℝ)^1049 := by
      have hnat : (2000545898481693829 : ℕ)^256*5000000000000000^1049 ≤ 5000333020962191^1049*2000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000545898481693829 2000000000000000000 5000333020962191 5000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000333020962191/5000000000000000 : ℝ)) (X := (2000545898481693829/2000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046414137524493493/100000000000000000000 : ℝ) ≤ (2500283125244089/2500000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (100046414137524493493/100000000000000000000 : ℝ)^256 ≤ (2500283125244089/2500000000000000 : ℝ)^1049 := by
      have hnat : (100046414137524493493 : ℕ)^256*2500000000000000^1049 ≤ 2500283125244089^1049*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046414137524493493 100000000000000000000 2500283125244089 2500000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500283125244089/2500000000000000 : ℝ)) (X := (100046414137524493493/100000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254095834435268471/6250000000000000000 : ℝ) ≤ (1000159896002833/1000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (6254095834435268471/6250000000000000000 : ℝ)^256 ≤ (1000159896002833/1000000000000000 : ℝ)^1049 := by
      have hnat : (6254095834435268471 : ℕ)^256*1000000000000000^1049 ≤ 1000159896002833^1049*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254095834435268471 6250000000000000000 1000159896002833 1000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000159896002833/1000000000000000 : ℝ)) (X := (6254095834435268471/6250000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(545898481693829/4000000000000000000 : ℝ) ≤ ((6787794125558981539/6790000000000000000 : ℝ)+2*(233229525987/135800000000000 : ℝ)*(11397/100000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (6787794125558981539/6790000000000000000 : ℝ)+2*(233229525987/135800000000000 : ℝ)*(11397/100000 : ℝ)=(5000333020962191/5000000000000000 : ℝ) by norm_num, show 1+2*(545898481693829/4000000000000000000 : ℝ)=(2000545898481693829/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4095834435268471/12500000000000000000 : ℝ)+(545898481693829/4000000000000000000 : ℝ) ≤ ((6787794125558981539/6790000000000000000 : ℝ)+(233229525987/135800000000000 : ℝ)*((14113/100000 : ℝ)+(11397/100000 : ℝ)))^(1049/256 : ℝ) := by
    rw [show (6787794125558981539/6790000000000000000 : ℝ)+(233229525987/135800000000000 : ℝ)*((14113/100000 : ℝ)+(11397/100000 : ℝ))=(2500283125244089/2500000000000000 : ℝ) by norm_num, show 1+(4095834435268471/12500000000000000000 : ℝ)+(545898481693829/4000000000000000000 : ℝ)=(100046414137524493493/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4095834435268471/12500000000000000000 : ℝ) ≤ ((6787794125558981539/6790000000000000000 : ℝ)+2*(233229525987/135800000000000 : ℝ)*(14113/100000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (6787794125558981539/6790000000000000000 : ℝ)+2*(233229525987/135800000000000 : ℝ)*(14113/100000 : ℝ)=(1000159896002833/1000000000000000 : ℝ) by norm_num, show 1+2*(4095834435268471/12500000000000000000 : ℝ)=(6254095834435268471/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6787794125558981539/6790000000000000000 : ℝ)*(X 1 0+X 2 0)+(233229525987/135800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (6787794125558981539/6790000000000000000 : ℝ)) (alpha := (233229525987/135800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6787794125558981539/6790000000000000000 : ℝ)*(X 0 1+X 2 1)+(233229525987/135800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (6787794125558981539/6790000000000000000 : ℝ)) (alpha := (233229525987/135800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6787794125558981539/6790000000000000000 : ℝ)*(X 0 2+X 1 2)+(233229525987/135800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (6787794125558981539/6790000000000000000 : ℝ)) (alpha := (233229525987/135800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2139432717/10000000000 : ℝ)*X 0 0+(5392227601/10000000000 : ℝ)*X 0 1+(2633195551/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672290207/5000000000 : ℝ)*X 1 0+(-2203248493/10000000000 : ℝ)*X 1 1+(2633195567/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344580467/10000000000 : ℝ)*X 2 0+(2633195519/5000000000 : ℝ)*X 2 1+(-2203248549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356553451/10000000000 : ℝ)*X 0 0+(4231759179/10000000000 : ℝ)*X 0 1+(35879673/80000000 : ℝ)*X 0 2+(4356553451/10000000000 : ℝ)*X 1 0+(4231759179/10000000000 : ℝ)*X 1 1+(35879673/80000000 : ℝ)*X 1 2+(4356553451/10000000000 : ℝ)*X 2 0+(4231759179/10000000000 : ℝ)*X 2 1+(35879673/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-534859371/2500000000 : ℝ)*X 0 0+(1316677269/2500000000 : ℝ)*X 0 1+(5391908499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312565511/10000000000 : ℝ)*X 1 0+(-2077731223/10000000000 : ℝ)*X 1 1+(1347977091/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656282779/5000000000 : ℝ)*X 2 0+(2695954173/5000000000 : ℝ)*X 2 1+(-129858199/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089140731/2500000000 : ℝ)*X 0 0+(4484319257/10000000000 : ℝ)*X 0 1+(4232401569/10000000000 : ℝ)*X 0 2+(1089140731/2500000000 : ℝ)*X 1 0+(4484319257/10000000000 : ℝ)*X 1 1+(4232401569/10000000000 : ℝ)*X 1 2+(1089140731/2500000000 : ℝ)*X 2 0+(4484319257/10000000000 : ℝ)*X 2 1+(4232401569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15202502639849135519793/3395000000000000000000000000 : ℝ) := by norm_num
    linear_combination (209546183/25000000000000 : ℝ)*(base19) + (741400963/100000000000000 : ℝ)*(base23) + (96016353/100000000000000 : ℝ)*(lower2) + (41271497/20000000000000 : ℝ)*(upper3) + (217113/10000000000000 : ℝ)*(lower4) + (2974083436120547/50000000000000 : ℝ)*(major0) + (2974083436120547/50000000000000 : ℝ)*(major1) + (1189633374448219/20000000000000 : ℝ)*(major2) + (3973421874345697/50000000000000 : ℝ)*(sp0) + (7946860106237729/100000000000000 : ℝ)*(sp1) + (3973430101510749/50000000000000 : ℝ)*(sp2) + (1974728735856991/50000000000000 : ℝ)*(sp3) + (17195731067/100000000000000 : ℝ)*(sp4) + (7589541043/50000000000000 : ℝ)*(sp7) + (3949472650796067/100000000000000 : ℝ)*(f.failure) + (7946860944422461/100000000000000 : ℝ)*(f.sum) + (34787508798057/13580000000000000000000000000 : ℝ)*base66 + (2552472132388706833/339500000000000000000000000000000 : ℝ)*base67 + (1212855383988790959/135800000000000000000000000000000 : ℝ)*base70 + (6508161713658293167/339500000000000000000000000000000 : ℝ)*base72 + (18154120346403/13580000000000000000000000000 : ℝ)*base73 + (2057116263184209041/135800000000000000000000000000000 : ℝ)*base75 + (5478734650327968167/339500000000000000000000000000000 : ℝ)*base78 + (7229532933838031833/339500000000000000000000000000000 : ℝ)*base79 + (14199449757499/3395000000000000000000000000 : ℝ)*base81 + (5220287/1000000000000000000000 : ℝ)*base89 + (5220287/1000000000000000000000 : ℝ)*base91 + (4779713/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (178793351875366827278897307/67900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (273693111/100000000000000 : ℝ)*(base19) + (441752037/100000000000000 : ℝ)*(base23) + (7638223/20000000000000 : ℝ)*(lower4) + (10784293/50000000000000 : ℝ)*(upper5) + (1195681003586429/20000000000000 : ℝ)*(major0) + (1195681003586429/20000000000000 : ℝ)*(major1) + (1195681003586429/20000000000000 : ℝ)*(major2) + (769018649/100000000000000 : ℝ)*(sp0) + (445274473/20000000000000 : ℝ)*(sp1) + (1614785287/25000000000000 : ℝ)*(sp2) + (998407369938657/12500000000000 : ℝ)*(sp4) + (798725722846243/10000000000000 : ℝ)*(sp5) + (7987252827634721/100000000000000 : ℝ)*(sp6) + (3969550219563501/100000000000000 : ℝ)*(sp7) + (3969550219563501/100000000000000 : ℝ)*(f.failure) + (3993629864263953/50000000000000 : ℝ)*(f.sum) + (8637671812523/1358000000000000000000000000 : ℝ)*base66 + (739007200943484231/135800000000000000000000000000000 : ℝ)*base67 + (255412027829284231/135800000000000000000000000000000 : ℝ)*base69 + (497830406771884231/135800000000000000000000000000000 : ℝ)*base71 + (1144076558347/1358000000000000000000000000 : ℝ)*base73 + (360325336841115769/135800000000000000000000000000000 : ℝ)*base76 + (68813138906684231/135800000000000000000000000000000 : ℝ)*base77 + (1528957987699515769/135800000000000000000000000000000 : ℝ)*base80 + (5232287819351/1358000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (6534161/1000000000000000000000 : ℝ)*base89 + (6534161/1000000000000000000000 : ℝ)*base91 + (6534161/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1200_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1200_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1200_s7_0 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139453529/10000000000 : ℝ)*x 0 + (2695989847/5000000000 : ℝ)*x 1 + (2633312671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139453529/10000000000 : ℝ)^8393 ≤ (13005951821737/100000000000000 : ℝ)^6345 := by
    have hnat : (2139453529 : ℕ)^8393*100000000000000^6345 ≤ 13005951821737^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139453529 10000000000 13005951821737 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695989847/5000000000 : ℝ)^8393 ≤ (22086841005561/50000000000000 : ℝ)^6345 := by
    have hnat : (2695989847 : ℕ)^8393*50000000000000^6345 ≤ 22086841005561^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695989847 5000000000 22086841005561 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633312671/5000000000 : ℝ)^8393 ≤ (42820366149881/100000000000000 : ℝ)^6345 := by
    have hnat : (2633312671 : ℕ)^8393*100000000000000^6345 ≤ 42820366149881^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633312671 5000000000 42820366149881 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139453529/10000000000 : ℝ), (2695989847/5000000000 : ℝ), (2633312671/5000000000 : ℝ)] ![(13005951821737/100000000000000 : ℝ), (22086841005561/50000000000000 : ℝ), (42820366149881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139453529/10000000000 : ℝ)|^8393 ≤ (13005951821737/100000000000000 : ℝ)^6345
        have hw : |(-2139453529/10000000000 : ℝ)|=(2139453529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695989847/5000000000 : ℝ)|^8393 ≤ (22086841005561/50000000000000 : ℝ)^6345
        have hw : |(2695989847/5000000000 : ℝ)|=(2695989847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633312671/5000000000 : ℝ)|^8393 ≤ (42820366149881/100000000000000 : ℝ)^6345
        have hw : |(2633312671/5000000000 : ℝ)|=(2633312671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s7_1 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344517963/10000000000 : ℝ)*x 0 + (-440604267/2000000000 : ℝ)*x 1 + (2633312671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344517963/10000000000 : ℝ)^8393 ≤ (43660080958931/100000000000000 : ℝ)^6345 := by
    have hnat : (5344517963 : ℕ)^8393*100000000000000^6345 ≤ 43660080958931^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344517963 10000000000 43660080958931 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440604267/2000000000 : ℝ)^8393 ≤ (6759776436329/50000000000000 : ℝ)^6345 := by
    have hnat : (440604267 : ℕ)^8393*50000000000000^6345 ≤ 6759776436329^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440604267 2000000000 6759776436329 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633312671/5000000000 : ℝ)^8393 ≤ (42820366149881/100000000000000 : ℝ)^6345 := by
    have hnat : (2633312671 : ℕ)^8393*100000000000000^6345 ≤ 42820366149881^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633312671 5000000000 42820366149881 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344517963/10000000000 : ℝ), (-440604267/2000000000 : ℝ), (2633312671/5000000000 : ℝ)] ![(43660080958931/100000000000000 : ℝ), (6759776436329/50000000000000 : ℝ), (42820366149881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344517963/10000000000 : ℝ)|^8393 ≤ (43660080958931/100000000000000 : ℝ)^6345
        have hw : |(5344517963/10000000000 : ℝ)|=(5344517963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440604267/2000000000 : ℝ)|^8393 ≤ (6759776436329/50000000000000 : ℝ)^6345
        have hw : |(-440604267/2000000000 : ℝ)|=(440604267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633312671/5000000000 : ℝ)|^8393 ≤ (42820366149881/100000000000000 : ℝ)^6345
        have hw : |(2633312671/5000000000 : ℝ)|=(2633312671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s7_2 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344517963/10000000000 : ℝ)*x 0 + (2633312671/5000000000 : ℝ)*x 1 + (-275377667/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344517963/10000000000 : ℝ)^8393 ≤ (43660080958931/100000000000000 : ℝ)^6345 := by
    have hnat : (5344517963 : ℕ)^8393*100000000000000^6345 ≤ 43660080958931^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344517963 10000000000 43660080958931 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633312671/5000000000 : ℝ)^8393 ≤ (42820366149881/100000000000000 : ℝ)^6345 := by
    have hnat : (2633312671 : ℕ)^8393*100000000000000^6345 ≤ 42820366149881^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633312671 5000000000 42820366149881 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275377667/1250000000 : ℝ)^8393 ≤ (540782115231/4000000000000 : ℝ)^6345 := by
    have hnat : (275377667 : ℕ)^8393*4000000000000^6345 ≤ 540782115231^6345*1250000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275377667 1250000000 540782115231 4000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344517963/10000000000 : ℝ), (2633312671/5000000000 : ℝ), (-275377667/1250000000 : ℝ)] ![(43660080958931/100000000000000 : ℝ), (42820366149881/100000000000000 : ℝ), (540782115231/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344517963/10000000000 : ℝ)|^8393 ≤ (43660080958931/100000000000000 : ℝ)^6345
        have hw : |(5344517963/10000000000 : ℝ)|=(5344517963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633312671/5000000000 : ℝ)|^8393 ≤ (42820366149881/100000000000000 : ℝ)^6345
        have hw : |(2633312671/5000000000 : ℝ)|=(2633312671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275377667/1250000000 : ℝ)|^8393 ≤ (540782115231/4000000000000 : ℝ)^6345
        have hw : |(-275377667/1250000000 : ℝ)|=(275377667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s7_3 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (68071337/156250000 : ℝ)*x 0 + (4232242873/10000000000 : ℝ)*x 1 + (2242236199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68071337/156250000 : ℝ)^8393 ≤ (4164659254841/12500000000000 : ℝ)^6345 := by
    have hnat : (68071337 : ℕ)^8393*12500000000000^6345 ≤ 4164659254841^6345*156250000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68071337 156250000 4164659254841 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232242873/10000000000 : ℝ)^8393 ≤ (4008181222143/12500000000000 : ℝ)^6345 := by
    have hnat : (4232242873 : ℕ)^8393*12500000000000^6345 ≤ 4008181222143^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232242873 10000000000 4008181222143 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242236199/5000000000 : ℝ)^8393 ≤ (34617276169243/100000000000000 : ℝ)^6345 := by
    have hnat : (2242236199 : ℕ)^8393*100000000000000^6345 ≤ 34617276169243^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242236199 5000000000 34617276169243 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68071337/156250000 : ℝ), (4232242873/10000000000 : ℝ), (2242236199/5000000000 : ℝ)] ![(4164659254841/12500000000000 : ℝ), (4008181222143/12500000000000 : ℝ), (34617276169243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68071337/156250000 : ℝ)|^8393 ≤ (4164659254841/12500000000000 : ℝ)^6345
        have hw : |(68071337/156250000 : ℝ)|=(68071337/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232242873/10000000000 : ℝ)|^8393 ≤ (4008181222143/12500000000000 : ℝ)^6345
        have hw : |(4232242873/10000000000 : ℝ)|=(4232242873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242236199/5000000000 : ℝ)|^8393 ≤ (34617276169243/100000000000000 : ℝ)^6345
        have hw : |(2242236199/5000000000 : ℝ)|=(2242236199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s7_4 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069729141/5000000000 : ℝ)*x 0 + (1316735243/2500000000 : ℝ)*x 1 + (5391662919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069729141/5000000000 : ℝ)^8393 ≤ (1625748755241/12500000000000 : ℝ)^6345 := by
    have hnat : (1069729141 : ℕ)^8393*12500000000000^6345 ≤ 1625748755241^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069729141 5000000000 1625748755241 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316735243/2500000000 : ℝ)^8393 ≤ (1338242522803/3125000000000 : ℝ)^6345 := by
    have hnat : (1316735243 : ℕ)^8393*3125000000000^6345 ≤ 1338242522803^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316735243 2500000000 1338242522803 3125000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391662919/10000000000 : ℝ)^8393 ≤ (11042562304303/25000000000000 : ℝ)^6345 := by
    have hnat : (5391662919 : ℕ)^8393*25000000000000^6345 ≤ 11042562304303^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391662919 10000000000 11042562304303 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069729141/5000000000 : ℝ), (1316735243/2500000000 : ℝ), (5391662919/10000000000 : ℝ)] ![(1625748755241/12500000000000 : ℝ), (1338242522803/3125000000000 : ℝ), (11042562304303/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069729141/5000000000 : ℝ)|^8393 ≤ (1625748755241/12500000000000 : ℝ)^6345
        have hw : |(-1069729141/5000000000 : ℝ)|=(1069729141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316735243/2500000000 : ℝ)|^8393 ≤ (1338242522803/3125000000000 : ℝ)^6345
        have hw : |(1316735243/2500000000 : ℝ)|=(1316735243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391662919/10000000000 : ℝ)|^8393 ≤ (11042562304303/25000000000000 : ℝ)^6345
        have hw : |(5391662919/10000000000 : ℝ)|=(5391662919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s7_5 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664078201/1250000000 : ℝ)*x 0 + (-25974797/125000000 : ℝ)*x 1 + (5391662919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664078201/1250000000 : ℝ)^8393 ≤ (21657893592119/50000000000000 : ℝ)^6345 := by
    have hnat : (664078201 : ℕ)^8393*50000000000000^6345 ≤ 21657893592119^6345*1250000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664078201 1250000000 21657893592119 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25974797/125000000 : ℝ)^8393 ≤ (3128490896559/25000000000000 : ℝ)^6345 := by
    have hnat : (25974797 : ℕ)^8393*25000000000000^6345 ≤ 3128490896559^6345*125000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25974797 125000000 3128490896559 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391662919/10000000000 : ℝ)^8393 ≤ (11042562304303/25000000000000 : ℝ)^6345 := by
    have hnat : (5391662919 : ℕ)^8393*25000000000000^6345 ≤ 11042562304303^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391662919 10000000000 11042562304303 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664078201/1250000000 : ℝ), (-25974797/125000000 : ℝ), (5391662919/10000000000 : ℝ)] ![(21657893592119/50000000000000 : ℝ), (3128490896559/25000000000000 : ℝ), (11042562304303/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664078201/1250000000 : ℝ)|^8393 ≤ (21657893592119/50000000000000 : ℝ)^6345
        have hw : |(664078201/1250000000 : ℝ)|=(664078201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25974797/125000000 : ℝ)|^8393 ≤ (3128490896559/25000000000000 : ℝ)^6345
        have hw : |(-25974797/125000000 : ℝ)|=(25974797/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391662919/10000000000 : ℝ)|^8393 ≤ (11042562304303/25000000000000 : ℝ)^6345
        have hw : |(5391662919/10000000000 : ℝ)|=(5391662919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s7_6 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664078201/1250000000 : ℝ)*x 0 + (5391662919/10000000000 : ℝ)*x 1 + (-25974797/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664078201/1250000000 : ℝ)^8393 ≤ (21657893592119/50000000000000 : ℝ)^6345 := by
    have hnat : (664078201 : ℕ)^8393*50000000000000^6345 ≤ 21657893592119^6345*1250000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664078201 1250000000 21657893592119 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391662919/10000000000 : ℝ)^8393 ≤ (11042562304303/25000000000000 : ℝ)^6345 := by
    have hnat : (5391662919 : ℕ)^8393*25000000000000^6345 ≤ 11042562304303^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391662919 10000000000 11042562304303 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25974797/125000000 : ℝ)^8393 ≤ (3128490896559/25000000000000 : ℝ)^6345 := by
    have hnat : (25974797 : ℕ)^8393*25000000000000^6345 ≤ 3128490896559^6345*125000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25974797 125000000 3128490896559 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664078201/1250000000 : ℝ), (5391662919/10000000000 : ℝ), (-25974797/125000000 : ℝ)] ![(21657893592119/50000000000000 : ℝ), (11042562304303/25000000000000 : ℝ), (3128490896559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664078201/1250000000 : ℝ)|^8393 ≤ (21657893592119/50000000000000 : ℝ)^6345
        have hw : |(664078201/1250000000 : ℝ)|=(664078201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391662919/10000000000 : ℝ)|^8393 ≤ (11042562304303/25000000000000 : ℝ)^6345
        have hw : |(5391662919/10000000000 : ℝ)|=(5391662919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25974797/125000000 : ℝ)|^8393 ≤ (3128490896559/25000000000000 : ℝ)^6345
        have hw : |(-25974797/125000000 : ℝ)|=(25974797/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s7_7 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356575127/10000000000 : ℝ)*x 0 + (4483837307/10000000000 : ℝ)*x 1 + (4232880263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356575127/10000000000 : ℝ)^8393 ≤ (260291958891/781250000000 : ℝ)^6345 := by
    have hnat : (4356575127 : ℕ)^8393*781250000000^6345 ≤ 260291958891^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356575127 10000000000 260291958891 781250000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483837307/10000000000 : ℝ)^8393 ≤ (6922158284063/20000000000000 : ℝ)^6345 := by
    have hnat : (4483837307 : ℕ)^8393*20000000000000^6345 ≤ 6922158284063^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483837307 10000000000 6922158284063 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232880263/10000000000 : ℝ)^8393 ≤ (4008979728107/12500000000000 : ℝ)^6345 := by
    have hnat : (4232880263 : ℕ)^8393*12500000000000^6345 ≤ 4008979728107^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232880263 10000000000 4008979728107 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356575127/10000000000 : ℝ), (4483837307/10000000000 : ℝ), (4232880263/10000000000 : ℝ)] ![(260291958891/781250000000 : ℝ), (6922158284063/20000000000000 : ℝ), (4008979728107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356575127/10000000000 : ℝ)|^8393 ≤ (260291958891/781250000000 : ℝ)^6345
        have hw : |(4356575127/10000000000 : ℝ)|=(4356575127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483837307/10000000000 : ℝ)|^8393 ≤ (6922158284063/20000000000000 : ℝ)^6345
        have hw : |(4483837307/10000000000 : ℝ)|=(4483837307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232880263/10000000000 : ℝ)|^8393 ≤ (4008979728107/12500000000000 : ℝ)^6345
        have hw : |(4232880263/10000000000 : ℝ)|=(4232880263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1200_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11427/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7041/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5711/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5711/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5711/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5711/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5711/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5711/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5711/50000 : ℝ) ^ (1049/256 : ℝ) ≤ (13770549025354967/100000000000000000000 : ℝ) := by
    have hpowers : (5711/50000 : ℝ)^1049 ≤ (13770549025354967/100000000000000000000 : ℝ)^256 := by
      have hnat : (5711 : ℕ)^1049*100000000000000000000^256 ≤ 13770549025354967^256*50000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5711 50000 13770549025354967 100000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5711/50000 : ℝ)) (X := (13770549025354967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14087/100000 : ℝ) ^ (1049/256 : ℝ) ≤ (32520024676933657/100000000000000000000 : ℝ) := by
    have hpowers : (14087/100000 : ℝ)^1049 ≤ (32520024676933657/100000000000000000000 : ℝ)^256 := by
      have hnat : (14087 : ℕ)^1049*100000000000000000000^256 ≤ 32520024676933657^256*100000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14087 100000 32520024676933657 100000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14087/100000 : ℝ)) (X := (32520024676933657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013770549025354967/50000000000000000000 : ℝ) ≤ (10000672048356819/10000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (50013770549025354967/50000000000000000000 : ℝ)^256 ≤ (10000672048356819/10000000000000000 : ℝ)^1049 := by
      have hnat : (50013770549025354967 : ℕ)^256*10000000000000000^1049 ≤ 10000672048356819^1049*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013770549025354967 50000000000000000000 10000672048356819 10000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000672048356819/10000000000000000 : ℝ)) (X := (50013770549025354967/50000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252893160856393039/6250000000000000000 : ℝ) ≤ (2000225897311403/2000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (6252893160856393039/6250000000000000000 : ℝ)^256 ≤ (2000225897311403/2000000000000000 : ℝ)^1049 := by
      have hnat : (6252893160856393039 : ℕ)^256*2000000000000000^1049 ≤ 2000225897311403^1049*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252893160856393039 6250000000000000000 2000225897311403 2000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000225897311403/2000000000000000 : ℝ)) (X := (6252893160856393039/6250000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032520024676933657/50000000000000000000 : ℝ) ≤ (10001586924757211/10000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (50032520024676933657/50000000000000000000 : ℝ)^256 ≤ (10001586924757211/10000000000000000 : ℝ)^1049 := by
      have hnat : (50032520024676933657 : ℕ)^256*10000000000000000^1049 ≤ 10001586924757211^1049*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032520024676933657 50000000000000000000 10001586924757211 10000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001586924757211/10000000000000000 : ℝ)) (X := (50032520024676933657/50000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13770549025354967/100000000000000000000 : ℝ) ≤ ((26641341290625645211/26650000000000000000 : ℝ)+2*(114359550049/66625000000000 : ℝ)*(5711/50000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (26641341290625645211/26650000000000000000 : ℝ)+2*(114359550049/66625000000000 : ℝ)*(5711/50000 : ℝ)=(10000672048356819/10000000000000000 : ℝ) by norm_num, show 1+2*(13770549025354967/100000000000000000000 : ℝ)=(50013770549025354967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32520024676933657/100000000000000000000 : ℝ)+(13770549025354967/100000000000000000000 : ℝ) ≤ ((26641341290625645211/26650000000000000000 : ℝ)+(114359550049/66625000000000 : ℝ)*((14087/100000 : ℝ)+(5711/50000 : ℝ)))^(1049/256 : ℝ) := by
    rw [show (26641341290625645211/26650000000000000000 : ℝ)+(114359550049/66625000000000 : ℝ)*((14087/100000 : ℝ)+(5711/50000 : ℝ))=(2000225897311403/2000000000000000 : ℝ) by norm_num, show 1+(32520024676933657/100000000000000000000 : ℝ)+(13770549025354967/100000000000000000000 : ℝ)=(6252893160856393039/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32520024676933657/100000000000000000000 : ℝ) ≤ ((26641341290625645211/26650000000000000000 : ℝ)+2*(114359550049/66625000000000 : ℝ)*(14087/100000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (26641341290625645211/26650000000000000000 : ℝ)+2*(114359550049/66625000000000 : ℝ)*(14087/100000 : ℝ)=(10001586924757211/10000000000000000 : ℝ) by norm_num, show 1+2*(32520024676933657/100000000000000000000 : ℝ)=(50032520024676933657/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26641341290625645211/26650000000000000000 : ℝ)*(X 1 0+X 2 0)+(114359550049/66625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (26641341290625645211/26650000000000000000 : ℝ)) (alpha := (114359550049/66625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26641341290625645211/26650000000000000000 : ℝ)*(X 0 1+X 2 1)+(114359550049/66625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (26641341290625645211/26650000000000000000 : ℝ)) (alpha := (114359550049/66625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26641341290625645211/26650000000000000000 : ℝ)*(X 0 2+X 1 2)+(114359550049/66625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (26641341290625645211/26650000000000000000 : ℝ)) (alpha := (114359550049/66625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2139453529/10000000000 : ℝ)*X 0 0+(2695989847/5000000000 : ℝ)*X 0 1+(2633312671/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344517963/10000000000 : ℝ)*X 1 0+(-440604267/2000000000 : ℝ)*X 1 1+(2633312671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344517963/10000000000 : ℝ)*X 2 0+(2633312671/5000000000 : ℝ)*X 2 1+(-275377667/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((68071337/156250000 : ℝ)*X 0 0+(4232242873/10000000000 : ℝ)*X 0 1+(2242236199/5000000000 : ℝ)*X 0 2+(68071337/156250000 : ℝ)*X 1 0+(4232242873/10000000000 : ℝ)*X 1 1+(2242236199/5000000000 : ℝ)*X 1 2+(68071337/156250000 : ℝ)*X 2 0+(4232242873/10000000000 : ℝ)*X 2 1+(2242236199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1069729141/5000000000 : ℝ)*X 0 0+(1316735243/2500000000 : ℝ)*X 0 1+(5391662919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664078201/1250000000 : ℝ)*X 1 0+(-25974797/125000000 : ℝ)*X 1 1+(5391662919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664078201/1250000000 : ℝ)*X 2 0+(5391662919/10000000000 : ℝ)*X 2 1+(-25974797/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356575127/10000000000 : ℝ)*X 0 0+(4483837307/10000000000 : ℝ)*X 0 1+(4232880263/10000000000 : ℝ)*X 0 2+(4356575127/10000000000 : ℝ)*X 1 0+(4483837307/10000000000 : ℝ)*X 1 1+(4232880263/10000000000 : ℝ)*X 1 2+(4356575127/10000000000 : ℝ)*X 2 0+(4483837307/10000000000 : ℝ)*X 2 1+(4232880263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5707117560203869421445164367/1332500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (839699119/100000000000000 : ℝ)*(base19) + (389217689/50000000000000 : ℝ)*(base23) + (32742517/100000000000000 : ℝ)*(lower2) + (54383401/50000000000000 : ℝ)*(upper3) + (62728543/100000000000000 : ℝ)*(upper5) + (1492762456288221/25000000000000 : ℝ)*(major0) + (1492762456288221/25000000000000 : ℝ)*(major1) + (1194209965030577/20000000000000 : ℝ)*(major2) + (99717623889657/1250000000000 : ℝ)*(sp0) + (7977432160072723/100000000000000 : ℝ)*(sp1) + (498589513833529/6250000000000 : ℝ)*(sp2) + (495581756524169/12500000000000 : ℝ)*(sp3) + (11544299641/50000000000000 : ℝ)*(sp4) + (2491114679/20000000000000 : ℝ)*(sp7) + (3964666507766747/100000000000000 : ℝ)*(f.failure) + (7977432999771843/100000000000000 : ℝ)*(f.sum) + (1426650525163/13325000000000000000000000000 : ℝ)*base66 + (380780364265390369/666250000000000000000000000000000 : ℝ)*base68 + (5803530092026896747/533000000000000000000000000000000 : ℝ)*base69 + (9440625782996640369/666250000000000000000000000000000 : ℝ)*base72 + (32802047735831/6662500000000000000000000000 : ℝ)*base73 + (5977124680622896747/533000000000000000000000000000000 : ℝ)*base75 + (5624508510175290369/666250000000000000000000000000000 : ℝ)*base78 + (4467749673039709631/666250000000000000000000000000000 : ℝ)*base79 + (23499928614239/13325000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3639767/1000000000000000000000 : ℝ)*base89 + (3639767/1000000000000000000000 : ℝ)*base91 + (6360233/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5655507430861478342915135973/1332500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48098817/6250000000000 : ℝ)*(base19) + (167344329/20000000000000 : ℝ)*(base23) + (1703591/2000000000000 : ℝ)*(upper3) + (1530897/5000000000000 : ℝ)*(lower4) + (5453687/6250000000000 : ℝ)*(upper5) + (6001289928079673/100000000000000 : ℝ)*(major0) + (6001289928079673/100000000000000 : ℝ)*(major1) + (6001289928079673/100000000000000 : ℝ)*(major2) + (5387767319/25000000000000 : ℝ)*(sp1) + (2891867383/12500000000000 : ℝ)*(sp2) + (2004458584645191/25000000000000 : ℝ)*(sp4) + (501113251120651/6250000000000 : ℝ)*(sp5) + (4008905183460027/50000000000000 : ℝ)*(sp6) + (1992372688051233/50000000000000 : ℝ)*(sp7) + (1992372688051233/50000000000000 : ℝ)*(f.failure) + (2004458584645191/25000000000000 : ℝ)*(f.sum) + (18927606530179/6662500000000000000000000000 : ℝ)*base65 + (4258559122879696003/2665000000000000000000000000000000 : ℝ)*base67 + (35926868707219696003/2665000000000000000000000000000000 : ℝ)*base69 + (12896092680259696003/2665000000000000000000000000000000 : ℝ)*base71 + (27997551624371/6662500000000000000000000000 : ℝ)*base74 + (17529983071519696003/2665000000000000000000000000000000 : ℝ)*base75 + (145528771839696003/2665000000000000000000000000000000 : ℝ)*base77 + (48937883998389696003/2665000000000000000000000000000000 : ℝ)*base79 + (19725288835321/6662500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5845013/500000000000000000000 : ℝ)*base89 + (5845013/500000000000000000000 : ℝ)*base91 + (5845013/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1200_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1200_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1200_s8_0 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139456971/10000000000 : ℝ)*x 0 + (1078386361/2000000000 : ℝ)*x 1 + (2633335511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139456971/10000000000 : ℝ)^8393 ≤ (13005979499811/100000000000000 : ℝ)^6345 := by
    have hnat : (2139456971 : ℕ)^8393*100000000000000^6345 ≤ 13005979499811^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139456971 10000000000 13005979499811 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078386361/2000000000 : ℝ)^8393 ≤ (44173163048481/100000000000000 : ℝ)^6345 := by
    have hnat : (1078386361 : ℕ)^8393*100000000000000^6345 ≤ 44173163048481^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078386361 2000000000 44173163048481 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633335511/5000000000 : ℝ)^8393 ≤ (21410428715601/50000000000000 : ℝ)^6345 := by
    have hnat : (2633335511 : ℕ)^8393*50000000000000^6345 ≤ 21410428715601^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633335511 5000000000 21410428715601 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139456971/10000000000 : ℝ), (1078386361/2000000000 : ℝ), (2633335511/5000000000 : ℝ)] ![(13005979499811/100000000000000 : ℝ), (44173163048481/100000000000000 : ℝ), (21410428715601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139456971/10000000000 : ℝ)|^8393 ≤ (13005979499811/100000000000000 : ℝ)^6345
        have hw : |(-2139456971/10000000000 : ℝ)|=(2139456971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078386361/2000000000 : ℝ)|^8393 ≤ (44173163048481/100000000000000 : ℝ)^6345
        have hw : |(1078386361/2000000000 : ℝ)|=(1078386361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633335511/5000000000 : ℝ)|^8393 ≤ (21410428715601/50000000000000 : ℝ)^6345
        have hw : |(2633335511/5000000000 : ℝ)|=(2633335511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s8_1 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668063259/1250000000 : ℝ)*x 0 + (-1101488343/5000000000 : ℝ)*x 1 + (526667099/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668063259/1250000000 : ℝ)^8393 ≤ (10914988116457/25000000000000 : ℝ)^6345 := by
    have hnat : (668063259 : ℕ)^8393*25000000000000^6345 ≤ 10914988116457^6345*1250000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668063259 1250000000 10914988116457 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101488343/5000000000 : ℝ)^8393 ≤ (6759595214903/50000000000000 : ℝ)^6345 := by
    have hnat : (1101488343 : ℕ)^8393*50000000000000^6345 ≤ 6759595214903^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101488343 5000000000 6759595214903 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526667099/1000000000 : ℝ)^8393 ≤ (21410428543523/50000000000000 : ℝ)^6345 := by
    have hnat : (526667099 : ℕ)^8393*50000000000000^6345 ≤ 21410428543523^6345*1000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526667099 1000000000 21410428543523 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668063259/1250000000 : ℝ), (-1101488343/5000000000 : ℝ), (526667099/1000000000 : ℝ)] ![(10914988116457/25000000000000 : ℝ), (6759595214903/50000000000000 : ℝ), (21410428543523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668063259/1250000000 : ℝ)|^8393 ≤ (10914988116457/25000000000000 : ℝ)^6345
        have hw : |(668063259/1250000000 : ℝ)|=(668063259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101488343/5000000000 : ℝ)|^8393 ≤ (6759595214903/50000000000000 : ℝ)^6345
        have hw : |(-1101488343/5000000000 : ℝ)|=(1101488343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526667099/1000000000 : ℝ)|^8393 ≤ (21410428543523/50000000000000 : ℝ)^6345
        have hw : |(526667099/1000000000 : ℝ)|=(526667099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s8_2 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336126517/2500000000 : ℝ)*x 0 + (5266671029/10000000000 : ℝ)*x 1 + (-3442151/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336126517/2500000000 : ℝ)^8393 ≤ (8731990484521/20000000000000 : ℝ)^6345 := by
    have hnat : (1336126517 : ℕ)^8393*20000000000000^6345 ≤ 8731990484521^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336126517 2500000000 8731990484521 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266671029/10000000000 : ℝ)^8393 ≤ (21410428753243/50000000000000 : ℝ)^6345 := by
    have hnat : (5266671029 : ℕ)^8393*50000000000000^6345 ≤ 21410428753243^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266671029 10000000000 21410428753243 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3442151/15625000 : ℝ)^8393 ≤ (6759595028199/50000000000000 : ℝ)^6345 := by
    have hnat : (3442151 : ℕ)^8393*50000000000000^6345 ≤ 6759595028199^6345*15625000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3442151 15625000 6759595028199 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336126517/2500000000 : ℝ), (5266671029/10000000000 : ℝ), (-3442151/15625000 : ℝ)] ![(8731990484521/20000000000000 : ℝ), (21410428753243/50000000000000 : ℝ), (6759595028199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336126517/2500000000 : ℝ)|^8393 ≤ (8731990484521/20000000000000 : ℝ)^6345
        have hw : |(1336126517/2500000000 : ℝ)|=(1336126517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266671029/10000000000 : ℝ)|^8393 ≤ (21410428753243/50000000000000 : ℝ)^6345
        have hw : |(5266671029/10000000000 : ℝ)|=(5266671029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3442151/15625000 : ℝ)|^8393 ≤ (6759595028199/50000000000000 : ℝ)^6345
        have hw : |(-3442151/15625000 : ℝ)|=(3442151/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s8_3 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356567969/10000000000 : ℝ)*x 0 + (3306513/7812500 : ℝ)*x 1 + (1121094497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356567969/10000000000 : ℝ)^8393 ≤ (33317298327357/100000000000000 : ℝ)^6345 := by
    have hnat : (4356567969 : ℕ)^8393*100000000000000^6345 ≤ 33317298327357^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356567969 10000000000 33317298327357 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3306513/7812500 : ℝ)^8393 ≤ (32066389508947/100000000000000 : ℝ)^6345 := by
    have hnat : (3306513 : ℕ)^8393*100000000000000^6345 ≤ 32066389508947^6345*7812500^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3306513 7812500 32066389508947 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121094497/2500000000 : ℝ)^8393 ≤ (34616312154543/100000000000000 : ℝ)^6345 := by
    have hnat : (1121094497 : ℕ)^8393*100000000000000^6345 ≤ 34616312154543^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121094497 2500000000 34616312154543 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356567969/10000000000 : ℝ), (3306513/7812500 : ℝ), (1121094497/2500000000 : ℝ)] ![(33317298327357/100000000000000 : ℝ), (32066389508947/100000000000000 : ℝ), (34616312154543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356567969/10000000000 : ℝ)|^8393 ≤ (33317298327357/100000000000000 : ℝ)^6345
        have hw : |(4356567969/10000000000 : ℝ)|=(4356567969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3306513/7812500 : ℝ)|^8393 ≤ (32066389508947/100000000000000 : ℝ)^6345
        have hw : |(3306513/7812500 : ℝ)|=(3306513/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121094497/2500000000 : ℝ)|^8393 ≤ (34616312154543/100000000000000 : ℝ)^6345
        have hw : |(1121094497/2500000000 : ℝ)|=(1121094497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s8_4 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139461879/10000000000 : ℝ)*x 0 + (1316746517/2500000000 : ℝ)*x 1 + (5391615493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139461879/10000000000 : ℝ)^8393 ≤ (13006018966421/100000000000000 : ℝ)^6345 := by
    have hnat : (2139461879 : ℕ)^8393*100000000000000^6345 ≤ 13006018966421^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139461879 10000000000 13006018966421 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316746517/2500000000 : ℝ)^8393 ≤ (1070606143489/2500000000000 : ℝ)^6345 := by
    have hnat : (1316746517 : ℕ)^8393*2500000000000^6345 ≤ 1070606143489^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316746517 2500000000 1070606143489 2500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391615493/10000000000 : ℝ)^8393 ≤ (2208486764087/5000000000000 : ℝ)^6345 := by
    have hnat : (5391615493 : ℕ)^8393*5000000000000^6345 ≤ 2208486764087^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391615493 10000000000 2208486764087 5000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139461879/10000000000 : ℝ), (1316746517/2500000000 : ℝ), (5391615493/10000000000 : ℝ)] ![(13006018966421/100000000000000 : ℝ), (1070606143489/2500000000000 : ℝ), (2208486764087/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139461879/10000000000 : ℝ)|^8393 ≤ (13006018966421/100000000000000 : ℝ)^6345
        have hw : |(-2139461879/10000000000 : ℝ)|=(2139461879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316746517/2500000000 : ℝ)|^8393 ≤ (1070606143489/2500000000000 : ℝ)^6345
        have hw : |(1316746517/2500000000 : ℝ)|=(1316746517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391615493/10000000000 : ℝ)|^8393 ≤ (2208486764087/5000000000000 : ℝ)^6345
        have hw : |(5391615493/10000000000 : ℝ)|=(5391615493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s8_5 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328159379/2500000000 : ℝ)*x 0 + (-415606443/2000000000 : ℝ)*x 1 + (5391615447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328159379/2500000000 : ℝ)^8393 ≤ (10828978903197/25000000000000 : ℝ)^6345 := by
    have hnat : (1328159379 : ℕ)^8393*25000000000000^6345 ≤ 10828978903197^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328159379 2500000000 10828978903197 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415606443/2000000000 : ℝ)^8393 ≤ (1251434957847/10000000000000 : ℝ)^6345 := by
    have hnat : (415606443 : ℕ)^8393*10000000000000^6345 ≤ 1251434957847^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415606443 2000000000 1251434957847 10000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391615447/10000000000 : ℝ)^8393 ≤ (22084867391629/50000000000000 : ℝ)^6345 := by
    have hnat : (5391615447 : ℕ)^8393*50000000000000^6345 ≤ 22084867391629^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391615447 10000000000 22084867391629 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328159379/2500000000 : ℝ), (-415606443/2000000000 : ℝ), (5391615447/10000000000 : ℝ)] ![(10828978903197/25000000000000 : ℝ), (1251434957847/10000000000000 : ℝ), (22084867391629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328159379/2500000000 : ℝ)|^8393 ≤ (10828978903197/25000000000000 : ℝ)^6345
        have hw : |(1328159379/2500000000 : ℝ)|=(1328159379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415606443/2000000000 : ℝ)|^8393 ≤ (1251434957847/10000000000000 : ℝ)^6345
        have hw : |(-415606443/2000000000 : ℝ)|=(415606443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391615447/10000000000 : ℝ)|^8393 ≤ (22084867391629/50000000000000 : ℝ)^6345
        have hw : |(5391615447/10000000000 : ℝ)|=(5391615447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s8_6 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312637593/10000000000 : ℝ)*x 0 + (2695807713/5000000000 : ℝ)*x 1 + (-103901607/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312637593/10000000000 : ℝ)^8393 ≤ (21657958221619/50000000000000 : ℝ)^6345 := by
    have hnat : (5312637593 : ℕ)^8393*50000000000000^6345 ≤ 21657958221619^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312637593 10000000000 21657958221619 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695807713/5000000000 : ℝ)^8393 ≤ (4416973455569/10000000000000 : ℝ)^6345 := by
    have hnat : (2695807713 : ℕ)^8393*10000000000000^6345 ≤ 4416973455569^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695807713 5000000000 4416973455569 10000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103901607/500000000 : ℝ)^8393 ≤ (6257174490509/50000000000000 : ℝ)^6345 := by
    have hnat : (103901607 : ℕ)^8393*50000000000000^6345 ≤ 6257174490509^6345*500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103901607 500000000 6257174490509 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312637593/10000000000 : ℝ), (2695807713/5000000000 : ℝ), (-103901607/500000000 : ℝ)] ![(21657958221619/50000000000000 : ℝ), (4416973455569/10000000000000 : ℝ), (6257174490509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312637593/10000000000 : ℝ)|^8393 ≤ (21657958221619/50000000000000 : ℝ)^6345
        have hw : |(5312637593/10000000000 : ℝ)|=(5312637593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695807713/5000000000 : ℝ)|^8393 ≤ (4416973455569/10000000000000 : ℝ)^6345
        have hw : |(2695807713/5000000000 : ℝ)|=(2695807713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103901607/500000000 : ℝ)|^8393 ≤ (6257174490509/50000000000000 : ℝ)^6345
        have hw : |(-103901607/500000000 : ℝ)|=(103901607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s8_7 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089144389/2500000000 : ℝ)*x 0 + (4483743853/10000000000 : ℝ)*x 1 + (4232973019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089144389/2500000000 : ℝ)^8393 ≤ (4164674413743/12500000000000 : ℝ)^6345 := by
    have hnat : (1089144389 : ℕ)^8393*12500000000000^6345 ≤ 4164674413743^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089144389 2500000000 4164674413743 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483743853/10000000000 : ℝ)^8393 ≤ (17304918605431/50000000000000 : ℝ)^6345 := by
    have hnat : (4483743853 : ℕ)^8393*50000000000000^6345 ≤ 17304918605431^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483743853 10000000000 17304918605431 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232973019/10000000000 : ℝ)^8393 ≤ (16036383734789/50000000000000 : ℝ)^6345 := by
    have hnat : (4232973019 : ℕ)^8393*50000000000000^6345 ≤ 16036383734789^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232973019 10000000000 16036383734789 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089144389/2500000000 : ℝ), (4483743853/10000000000 : ℝ), (4232973019/10000000000 : ℝ)] ![(4164674413743/12500000000000 : ℝ), (17304918605431/50000000000000 : ℝ), (16036383734789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089144389/2500000000 : ℝ)|^8393 ≤ (4164674413743/12500000000000 : ℝ)^6345
        have hw : |(1089144389/2500000000 : ℝ)|=(1089144389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483743853/10000000000 : ℝ)|^8393 ≤ (17304918605431/50000000000000 : ℝ)^6345
        have hw : |(4483743853/10000000000 : ℝ)|=(4483743853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232973019/10000000000 : ℝ)|^8393 ≤ (16036383734789/50000000000000 : ℝ)^6345
        have hw : |(4232973019/10000000000 : ℝ)|=(4232973019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1200_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2857/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11427/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11427/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11427/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11427/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11427/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11427/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11427/100000 : ℝ) ^ (1049/256 : ℝ) ≤ (6897633391508403/50000000000000000000 : ℝ) := by
    have hpowers : (11427/100000 : ℝ)^1049 ≤ (6897633391508403/50000000000000000000 : ℝ)^256 := by
      have hnat : (11427 : ℕ)^1049*50000000000000000000^256 ≤ 6897633391508403^256*100000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11427 100000 6897633391508403 50000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11427/100000 : ℝ)) (X := (6897633391508403/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7041/50000 : ℝ) ^ (1049/256 : ℝ) ≤ (6494550641008949/20000000000000000000 : ℝ) := by
    have hpowers : (7041/50000 : ℝ)^1049 ≤ (6494550641008949/20000000000000000000 : ℝ)^256 := by
      have hnat : (7041 : ℕ)^1049*20000000000000000000^256 ≤ 6494550641008949^256*50000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7041 50000 6494550641008949 20000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7041/50000 : ℝ)) (X := (6494550641008949/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006897633391508403/25000000000000000000 : ℝ) ≤ (5000336627269703/5000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (25006897633391508403/25000000000000000000 : ℝ)^256 ≤ (5000336627269703/5000000000000000 : ℝ)^1049 := by
      have hnat : (25006897633391508403 : ℕ)^256*5000000000000000^1049 ≤ 5000336627269703^1049*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006897633391508403 25000000000000000000 5000336627269703 5000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000336627269703/5000000000000000 : ℝ)) (X := (25006897633391508403/25000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046268019988061551/100000000000000000000 : ℝ) ≤ (1000112893634427/1000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (100046268019988061551/100000000000000000000 : ℝ)^256 ≤ (1000112893634427/1000000000000000 : ℝ)^1049 := by
      have hnat : (100046268019988061551 : ℕ)^256*1000000000000000^1049 ≤ 1000112893634427^1049*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046268019988061551 100000000000000000000 1000112893634427 1000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000112893634427/1000000000000000 : ℝ)) (X := (100046268019988061551/100000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006494550641008949/10000000000000000000 : ℝ) ≤ (5000792309074567/5000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (10006494550641008949/10000000000000000000 : ℝ)^256 ≤ (5000792309074567/5000000000000000 : ℝ)^1049 := by
      have hnat : (10006494550641008949 : ℕ)^256*5000000000000000^1049 ≤ 5000792309074567^1049*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006494550641008949 10000000000000000000 5000792309074567 5000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000792309074567/5000000000000000 : ℝ)) (X := (10006494550641008949/10000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6897633391508403/50000000000000000000 : ℝ) ≤ ((4423562223138960179/4425000000000000000 : ℝ)+2*(7120028201/4148437500000 : ℝ)*(11427/100000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (4423562223138960179/4425000000000000000 : ℝ)+2*(7120028201/4148437500000 : ℝ)*(11427/100000 : ℝ)=(5000336627269703/5000000000000000 : ℝ) by norm_num, show 1+2*(6897633391508403/50000000000000000000 : ℝ)=(25006897633391508403/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6494550641008949/20000000000000000000 : ℝ)+(6897633391508403/50000000000000000000 : ℝ) ≤ ((4423562223138960179/4425000000000000000 : ℝ)+(7120028201/4148437500000 : ℝ)*((7041/50000 : ℝ)+(11427/100000 : ℝ)))^(1049/256 : ℝ) := by
    rw [show (4423562223138960179/4425000000000000000 : ℝ)+(7120028201/4148437500000 : ℝ)*((7041/50000 : ℝ)+(11427/100000 : ℝ))=(1000112893634427/1000000000000000 : ℝ) by norm_num, show 1+(6494550641008949/20000000000000000000 : ℝ)+(6897633391508403/50000000000000000000 : ℝ)=(100046268019988061551/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6494550641008949/20000000000000000000 : ℝ) ≤ ((4423562223138960179/4425000000000000000 : ℝ)+2*(7120028201/4148437500000 : ℝ)*(7041/50000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (4423562223138960179/4425000000000000000 : ℝ)+2*(7120028201/4148437500000 : ℝ)*(7041/50000 : ℝ)=(5000792309074567/5000000000000000 : ℝ) by norm_num, show 1+2*(6494550641008949/20000000000000000000 : ℝ)=(10006494550641008949/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4423562223138960179/4425000000000000000 : ℝ)*(X 1 0+X 2 0)+(7120028201/4148437500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (4423562223138960179/4425000000000000000 : ℝ)) (alpha := (7120028201/4148437500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4423562223138960179/4425000000000000000 : ℝ)*(X 0 1+X 2 1)+(7120028201/4148437500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (4423562223138960179/4425000000000000000 : ℝ)) (alpha := (7120028201/4148437500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4423562223138960179/4425000000000000000 : ℝ)*(X 0 2+X 1 2)+(7120028201/4148437500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (4423562223138960179/4425000000000000000 : ℝ)) (alpha := (7120028201/4148437500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2139456971/10000000000 : ℝ)*X 0 0+(1078386361/2000000000 : ℝ)*X 0 1+(2633335511/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668063259/1250000000 : ℝ)*X 1 0+(-1101488343/5000000000 : ℝ)*X 1 1+(526667099/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336126517/2500000000 : ℝ)*X 2 0+(5266671029/10000000000 : ℝ)*X 2 1+(-3442151/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356567969/10000000000 : ℝ)*X 0 0+(3306513/7812500 : ℝ)*X 0 1+(1121094497/2500000000 : ℝ)*X 0 2+(4356567969/10000000000 : ℝ)*X 1 0+(3306513/7812500 : ℝ)*X 1 1+(1121094497/2500000000 : ℝ)*X 1 2+(4356567969/10000000000 : ℝ)*X 2 0+(3306513/7812500 : ℝ)*X 2 1+(1121094497/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2139461879/10000000000 : ℝ)*X 0 0+(1316746517/2500000000 : ℝ)*X 0 1+(5391615493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328159379/2500000000 : ℝ)*X 1 0+(-415606443/2000000000 : ℝ)*X 1 1+(5391615447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312637593/10000000000 : ℝ)*X 2 0+(2695807713/5000000000 : ℝ)*X 2 1+(-103901607/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089144389/2500000000 : ℝ)*X 0 0+(4483743853/10000000000 : ℝ)*X 0 1+(4232973019/10000000000 : ℝ)*X 0 2+(1089144389/2500000000 : ℝ)*X 1 0+(4483743853/10000000000 : ℝ)*X 1 1+(4232973019/10000000000 : ℝ)*X 1 2+(1089144389/2500000000 : ℝ)*X 2 0+(4483743853/10000000000 : ℝ)*X 2 1+(4232973019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2404488452045668741157887/625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (417979537/50000000000000 : ℝ)*(base19) + (770621861/100000000000000 : ℝ)*(base23) + (15863079/50000000000000 : ℝ)*(lower2) + (74506803/100000000000000 : ℝ)*(upper3) + (52479703/50000000000000 : ℝ)*(upper5) + (5975508153939053/100000000000000 : ℝ)*(major0) + (5975508153939053/100000000000000 : ℝ)*(major1) + (2987754076969527/50000000000000 : ℝ)*(major2) + (7983365762946769/100000000000000 : ℝ)*(sp0) + (1995847147040343/25000000000000 : ℝ)*(sp1) + (1596677730699717/20000000000000 : ℝ)*(sp2) + (3967614992487461/100000000000000 : ℝ)*(sp3) + (23661173677/100000000000000 : ℝ)*(sp4) + (11763030809/100000000000000 : ℝ)*(sp7) + (396762675551827/10000000000000 : ℝ)*(f.failure) + (3991694712060223/50000000000000 : ℝ)*(f.sum) + (30341401672801/13275000000000000000000000000 : ℝ)*base66 + (1959275385759143171/147500000000000000000000000000000 : ℝ)*base68 + (3805101956229304001/663750000000000000000000000000000 : ℝ)*base70 + (255038570361643171/147500000000000000000000000000000 : ℝ)*base72 + (54748036023151/13275000000000000000000000000 : ℝ)*base74 + (14593158545143054001/663750000000000000000000000000000 : ℝ)*base76 + (1674905149312011461/1327500000000000000000000000000000 : ℝ)*base77 + (4205573106914511461/1327500000000000000000000000000000 : ℝ)*base79 + (20736339726067/13275000000000000000000000000 : ℝ)*base81 + (1377647/100000000000000000000 : ℝ)*base89 + (1377647/100000000000000000000 : ℝ)*base91 + (377647/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63234187909500212005587491/22125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1020507791/100000000000000 : ℝ)*(base19) + (682026699/50000000000000 : ℝ)*(base23) + (11882521/4000000000000 : ℝ)*(lower1) + (90368631/100000000000000 : ℝ)*(upper2) + (4259903/3125000000000 : ℝ)*(upper3) + (81099519/50000000000000 : ℝ)*(upper5) + (600572802241243/10000000000000 : ℝ)*(major0) + (600572802241243/10000000000000 : ℝ)*(major1) + (600572802241243/10000000000000 : ℝ)*(major2) + (1190899741/12500000000000 : ℝ)*(sp2) + (4011881880502567/50000000000000 : ℝ)*(sp4) + (4011881370248671/50000000000000 : ℝ)*(sp5) + (501484554359613/6250000000000 : ℝ)*(sp6) + (1993846094275819/50000000000000 : ℝ)*(sp7) + (1993846094275819/50000000000000 : ℝ)*(f.failure) + (4011881880502567/50000000000000 : ℝ)*(f.sum) + (4686328742053/1327500000000000000000000000 : ℝ)*base66 + (1917169430293512509/132750000000000000000000000000000 : ℝ)*base68 + (529553538056987491/132750000000000000000000000000000 : ℝ)*base69 + (502607317317012509/132750000000000000000000000000000 : ℝ)*base72 + (163514736029/663750000000000000000000000 : ℝ)*base74 + (1609780005263987491/132750000000000000000000000000000 : ℝ)*base75 + (1652388092331012509/132750000000000000000000000000000 : ℝ)*base78 + (925128283105512509/132750000000000000000000000000000 : ℝ)*base80 + (19143737737097/1327500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (456359/500000000000000000000 : ℝ)*base89 + (456359/500000000000000000000 : ℝ)*base91 + (456359/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1200_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2857/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1200_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1200_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2857/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1200_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1200_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1200_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2857/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1200_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

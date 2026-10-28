-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1163_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:41:07.46818+00:00
-- url     : https://prove2.me/submissions/3c79d61c-0bf9-485b-b2e5-101faf17d0a1

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
theorem support_rectangle_w1163_s6_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2156857057/10000000000 : ℝ)*x 0 + (2696478441/5000000000 : ℝ)*x 1 + (1316446627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156857057/10000000000 : ℝ)^2089 ≤ (2621591863829/20000000000000 : ℝ)^1577 := by
    have hnat : (2156857057 : ℕ)^2089*20000000000000^1577 ≤ 2621591863829^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156857057 10000000000 2621591863829 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696478441/5000000000 : ℝ)^2089 ≤ (44132647742141/100000000000000 : ℝ)^1577 := by
    have hnat : (2696478441 : ℕ)^2089*100000000000000^1577 ≤ 44132647742141^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696478441 5000000000 44132647742141 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316446627/2500000000 : ℝ)^2089 ≤ (8551878584479/20000000000000 : ℝ)^1577 := by
    have hnat : (1316446627 : ℕ)^2089*20000000000000^1577 ≤ 8551878584479^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316446627 2500000000 8551878584479 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2156857057/10000000000 : ℝ), (2696478441/5000000000 : ℝ), (1316446627/2500000000 : ℝ)] ![(2621591863829/20000000000000 : ℝ), (44132647742141/100000000000000 : ℝ), (8551878584479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2156857057/10000000000 : ℝ)|^2089 ≤ (2621591863829/20000000000000 : ℝ)^1577
        have hw : |(-2156857057/10000000000 : ℝ)|=(2156857057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696478441/5000000000 : ℝ)|^2089 ≤ (44132647742141/100000000000000 : ℝ)^1577
        have hw : |(2696478441/5000000000 : ℝ)|=(2696478441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316446627/2500000000 : ℝ)|^2089 ≤ (8551878584479/20000000000000 : ℝ)^1577
        have hw : |(1316446627/2500000000 : ℝ)|=(1316446627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s6_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672376683/5000000000 : ℝ)*x 0 + (-2221359447/10000000000 : ℝ)*x 1 + (5265786623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672376683/5000000000 : ℝ)^2089 ≤ (2180543435863/5000000000000 : ℝ)^1577 := by
    have hnat : (2672376683 : ℕ)^2089*5000000000000^1577 ≤ 2180543435863^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672376683 5000000000 2180543435863 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2221359447/10000000000 : ℝ)^2089 ≤ (13629737113993/100000000000000 : ℝ)^1577 := by
    have hnat : (2221359447 : ℕ)^2089*100000000000000^1577 ≤ 13629737113993^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221359447 10000000000 13629737113993 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265786623/10000000000 : ℝ)^2089 ≤ (10689848539851/25000000000000 : ℝ)^1577 := by
    have hnat : (5265786623 : ℕ)^2089*25000000000000^1577 ≤ 10689848539851^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265786623 10000000000 10689848539851 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672376683/5000000000 : ℝ), (-2221359447/10000000000 : ℝ), (5265786623/10000000000 : ℝ)] ![(2180543435863/5000000000000 : ℝ), (13629737113993/100000000000000 : ℝ), (10689848539851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672376683/5000000000 : ℝ)|^2089 ≤ (2180543435863/5000000000000 : ℝ)^1577
        have hw : |(2672376683/5000000000 : ℝ)|=(2672376683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2221359447/10000000000 : ℝ)|^2089 ≤ (13629737113993/100000000000000 : ℝ)^1577
        have hw : |(-2221359447/10000000000 : ℝ)|=(2221359447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265786623/10000000000 : ℝ)|^2089 ≤ (10689848539851/25000000000000 : ℝ)^1577
        have hw : |(5265786623/10000000000 : ℝ)|=(5265786623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s6_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672376837/5000000000 : ℝ)*x 0 + (2632893069/5000000000 : ℝ)*x 1 + (-2221359679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672376837/5000000000 : ℝ)^2089 ≤ (43610872046343/100000000000000 : ℝ)^1577 := by
    have hnat : (2672376837 : ℕ)^2089*100000000000000^1577 ≤ 43610872046343^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672376837 5000000000 43610872046343 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632893069/5000000000 : ℝ)^2089 ≤ (42759388942453/100000000000000 : ℝ)^1577 := by
    have hnat : (2632893069 : ℕ)^2089*100000000000000^1577 ≤ 42759388942453^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632893069 5000000000 42759388942453 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2221359679/10000000000 : ℝ)^2089 ≤ (13629738999653/100000000000000 : ℝ)^1577 := by
    have hnat : (2221359679 : ℕ)^2089*100000000000000^1577 ≤ 13629738999653^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221359679 10000000000 13629738999653 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672376837/5000000000 : ℝ), (2632893069/5000000000 : ℝ), (-2221359679/10000000000 : ℝ)] ![(43610872046343/100000000000000 : ℝ), (42759388942453/100000000000000 : ℝ), (13629738999653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672376837/5000000000 : ℝ)|^2089 ≤ (43610872046343/100000000000000 : ℝ)^1577
        have hw : |(2672376837/5000000000 : ℝ)|=(2672376837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632893069/5000000000 : ℝ)|^2089 ≤ (42759388942453/100000000000000 : ℝ)^1577
        have hw : |(2632893069/5000000000 : ℝ)|=(2632893069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2221359679/10000000000 : ℝ)|^2089 ≤ (13629738999653/100000000000000 : ℝ)^1577
        have hw : |(-2221359679/10000000000 : ℝ)|=(2221359679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s6_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2180854227/5000000000 : ℝ)*x 0 + (529564531/1250000000 : ℝ)*x 1 + (898112493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180854227/5000000000 : ℝ)^2089 ≤ (1665846594083/5000000000000 : ℝ)^1577 := by
    have hnat : (2180854227 : ℕ)^2089*5000000000000^1577 ≤ 1665846594083^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180854227 5000000000 1665846594083 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529564531/1250000000 : ℝ)^2089 ≤ (32056118427527/100000000000000 : ℝ)^1577 := by
    have hnat : (529564531 : ℕ)^2089*100000000000000^1577 ≤ 32056118427527^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529564531 1250000000 32056118427527 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898112493/2000000000 : ℝ)^2089 ≤ (34626949678887/100000000000000 : ℝ)^1577 := by
    have hnat : (898112493 : ℕ)^2089*100000000000000^1577 ≤ 34626949678887^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898112493 2000000000 34626949678887 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180854227/5000000000 : ℝ), (529564531/1250000000 : ℝ), (898112493/2000000000 : ℝ)] ![(1665846594083/5000000000000 : ℝ), (32056118427527/100000000000000 : ℝ), (34626949678887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180854227/5000000000 : ℝ)|^2089 ≤ (1665846594083/5000000000000 : ℝ)^1577
        have hw : |(2180854227/5000000000 : ℝ)|=(2180854227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529564531/1250000000 : ℝ)|^2089 ≤ (32056118427527/100000000000000 : ℝ)^1577
        have hw : |(529564531/1250000000 : ℝ)|=(529564531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898112493/2000000000 : ℝ)|^2089 ≤ (34626949678887/100000000000000 : ℝ)^1577
        have hw : |(898112493/2000000000 : ℝ)|=(898112493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s6_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-269607787/1250000000 : ℝ)*x 0 + (105322147/200000000 : ℝ)*x 1 + (5392634619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269607787/1250000000 : ℝ)^2089 ≤ (26216002991/200000000000 : ℝ)^1577 := by
    have hnat : (269607787 : ℕ)^2089*200000000000^1577 ≤ 26216002991^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269607787 1250000000 26216002991 200000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105322147/200000000 : ℝ)^2089 ≤ (42762844125673/100000000000000 : ℝ)^1577 := by
    have hnat : (105322147 : ℕ)^2089*100000000000000^1577 ≤ 42762844125673^1577*200000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105322147 200000000 42762844125673 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392634619/10000000000 : ℝ)^2089 ≤ (5516144295081/12500000000000 : ℝ)^1577 := by
    have hnat : (5392634619 : ℕ)^2089*12500000000000^1577 ≤ 5516144295081^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392634619 10000000000 5516144295081 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269607787/1250000000 : ℝ), (105322147/200000000 : ℝ), (5392634619/10000000000 : ℝ)] ![(26216002991/200000000000 : ℝ), (42762844125673/100000000000000 : ℝ), (5516144295081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269607787/1250000000 : ℝ)|^2089 ≤ (26216002991/200000000000 : ℝ)^1577
        have hw : |(-269607787/1250000000 : ℝ)|=(269607787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105322147/200000000 : ℝ)|^2089 ≤ (42762844125673/100000000000000 : ℝ)^1577
        have hw : |(105322147/200000000 : ℝ)|=(105322147/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392634619/10000000000 : ℝ)|^2089 ≤ (5516144295081/12500000000000 : ℝ)^1577
        have hw : |(5392634619/10000000000 : ℝ)|=(5392634619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s6_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656242373/5000000000 : ℝ)*x 0 + (-1047255579/5000000000 : ℝ)*x 1 + (674079323/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656242373/5000000000 : ℝ)^2089 ≤ (21631214450647/50000000000000 : ℝ)^1577 := by
    have hnat : (2656242373 : ℕ)^2089*50000000000000^1577 ≤ 21631214450647^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656242373 5000000000 21631214450647 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047255579/5000000000 : ℝ)^2089 ≤ (12608417105929/100000000000000 : ℝ)^1577 := by
    have hnat : (1047255579 : ℕ)^2089*100000000000000^1577 ≤ 12608417105929^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047255579 5000000000 12608417105929 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674079323/1250000000 : ℝ)^2089 ≤ (22064576990623/50000000000000 : ℝ)^1577 := by
    have hnat : (674079323 : ℕ)^2089*50000000000000^1577 ≤ 22064576990623^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674079323 1250000000 22064576990623 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656242373/5000000000 : ℝ), (-1047255579/5000000000 : ℝ), (674079323/1250000000 : ℝ)] ![(21631214450647/50000000000000 : ℝ), (12608417105929/100000000000000 : ℝ), (22064576990623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656242373/5000000000 : ℝ)|^2089 ≤ (21631214450647/50000000000000 : ℝ)^1577
        have hw : |(2656242373/5000000000 : ℝ)|=(2656242373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1047255579/5000000000 : ℝ)|^2089 ≤ (12608417105929/100000000000000 : ℝ)^1577
        have hw : |(-1047255579/5000000000 : ℝ)|=(1047255579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674079323/1250000000 : ℝ)|^2089 ≤ (22064576990623/50000000000000 : ℝ)^1577
        have hw : |(674079323/1250000000 : ℝ)|=(674079323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s6_6 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132812119/250000000 : ℝ)*x 0 + (674079317/1250000000 : ℝ)*x 1 + (-523627801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132812119/250000000 : ℝ)^2089 ≤ (43262429052319/100000000000000 : ℝ)^1577 := by
    have hnat : (132812119 : ℕ)^2089*100000000000000^1577 ≤ 43262429052319^1577*250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132812119 250000000 43262429052319 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674079317/1250000000 : ℝ)^2089 ≤ (11032288365231/25000000000000 : ℝ)^1577 := by
    have hnat : (674079317 : ℕ)^2089*25000000000000^1577 ≤ 11032288365231^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674079317 1250000000 11032288365231 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523627801/2500000000 : ℝ)^2089 ≤ (630420873637/5000000000000 : ℝ)^1577 := by
    have hnat : (523627801 : ℕ)^2089*5000000000000^1577 ≤ 630420873637^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523627801 2500000000 630420873637 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132812119/250000000 : ℝ), (674079317/1250000000 : ℝ), (-523627801/2500000000 : ℝ)] ![(43262429052319/100000000000000 : ℝ), (11032288365231/25000000000000 : ℝ), (630420873637/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132812119/250000000 : ℝ)|^2089 ≤ (43262429052319/100000000000000 : ℝ)^1577
        have hw : |(132812119/250000000 : ℝ)|=(132812119/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674079317/1250000000 : ℝ)|^2089 ≤ (11032288365231/25000000000000 : ℝ)^1577
        have hw : |(674079317/1250000000 : ℝ)|=(674079317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-523627801/2500000000 : ℝ)|^2089 ≤ (630420873637/5000000000000 : ℝ)^1577
        have hw : |(-523627801/2500000000 : ℝ)|=(523627801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s6_7 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4361717787/10000000000 : ℝ)*x 0 + (179596827/400000000 : ℝ)*x 1 + (847432167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361717787/10000000000 : ℝ)^2089 ≤ (33317026317431/100000000000000 : ℝ)^1577 := by
    have hnat : (4361717787 : ℕ)^2089*100000000000000^1577 ≤ 33317026317431^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361717787 10000000000 33317026317431 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179596827/400000000 : ℝ)^2089 ≤ (17310197109909/50000000000000 : ℝ)^1577 := by
    have hnat : (179596827 : ℕ)^2089*50000000000000^1577 ≤ 17310197109909^1577*400000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179596827 400000000 17310197109909 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847432167/2000000000 : ℝ)^2089 ≤ (1603128972367/5000000000000 : ℝ)^1577 := by
    have hnat : (847432167 : ℕ)^2089*5000000000000^1577 ≤ 1603128972367^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847432167 2000000000 1603128972367 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361717787/10000000000 : ℝ), (179596827/400000000 : ℝ), (847432167/2000000000 : ℝ)] ![(33317026317431/100000000000000 : ℝ), (17310197109909/50000000000000 : ℝ), (1603128972367/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361717787/10000000000 : ℝ)|^2089 ≤ (33317026317431/100000000000000 : ℝ)^1577
        have hw : |(4361717787/10000000000 : ℝ)|=(4361717787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179596827/400000000 : ℝ)|^2089 ≤ (17310197109909/50000000000000 : ℝ)^1577
        have hw : |(179596827/400000000 : ℝ)|=(179596827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847432167/2000000000 : ℝ)|^2089 ≤ (1603128972367/5000000000000 : ℝ)^1577
        have hw : |(847432167/2000000000 : ℝ)|=(847432167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5687/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3517/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5673/50000 : ℝ) ^ (8355/2048 : ℝ) ≤ (6968129379027361/50000000000000000000 : ℝ) := by
    have hpowers : (5673/50000 : ℝ)^8355 ≤ (6968129379027361/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5673 : ℕ)^8355*50000000000000000000^2048 ≤ 6968129379027361^2048*50000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5673 50000 6968129379027361 50000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5673/50000 : ℝ)) (X := (6968129379027361/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14097/100000 : ℝ) ^ (8355/2048 : ℝ) ≤ (16894911854787859/50000000000000000000 : ℝ) := by
    have hpowers : (14097/100000 : ℝ)^8355 ≤ (16894911854787859/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14097 : ℕ)^8355*50000000000000000000^2048 ≤ 16894911854787859^2048*100000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14097 100000 16894911854787859 50000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14097/100000 : ℝ)) (X := (16894911854787859/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006968129379027361/25000000000000000000 : ℝ) ≤ (2000136629351609/2000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (25006968129379027361/25000000000000000000 : ℝ)^2048 ≤ (2000136629351609/2000000000000000 : ℝ)^8355 := by
      have hnat : (25006968129379027361 : ℕ)^2048*2000000000000000^8355 ≤ 2000136629351609^8355*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006968129379027361 25000000000000000000 2000136629351609 2000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000136629351609/2000000000000000 : ℝ)) (X := (25006968129379027361/25000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501193152061690761/2500000000000000000 : ℝ) ≤ (10001169663850443/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (2501193152061690761/2500000000000000000 : ℝ)^2048 ≤ (10001169663850443/10000000000000000 : ℝ)^8355 := by
      have hnat : (2501193152061690761 : ℕ)^2048*10000000000000000^8355 ≤ 10001169663850443^8355*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501193152061690761 2500000000000000000 10001169663850443 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001169663850443/10000000000000000 : ℝ)) (X := (2501193152061690761/2500000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016894911854787859/25000000000000000000 : ℝ) ≤ (10001656180942841/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (25016894911854787859/25000000000000000000 : ℝ)^2048 ≤ (10001656180942841/10000000000000000 : ℝ)^8355 := by
      have hnat : (25016894911854787859 : ℕ)^2048*10000000000000000^8355 ≤ 10001656180942841^8355*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016894911854787859 25000000000000000000 10001656180942841 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001656180942841/10000000000000000 : ℝ)) (X := (25016894911854787859/25000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6968129379027361/50000000000000000000 : ℝ) ≤ ((9166946430290228793/9170000000000000000 : ℝ)+2*(243258546199/137550000000000 : ℝ)*(5673/50000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (9166946430290228793/9170000000000000000 : ℝ)+2*(243258546199/137550000000000 : ℝ)*(5673/50000 : ℝ)=(2000136629351609/2000000000000000 : ℝ) by norm_num, show 1+2*(6968129379027361/50000000000000000000 : ℝ)=(25006968129379027361/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16894911854787859/50000000000000000000 : ℝ)+(6968129379027361/50000000000000000000 : ℝ) ≤ ((9166946430290228793/9170000000000000000 : ℝ)+(243258546199/137550000000000 : ℝ)*((14097/100000 : ℝ)+(5673/50000 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (9166946430290228793/9170000000000000000 : ℝ)+(243258546199/137550000000000 : ℝ)*((14097/100000 : ℝ)+(5673/50000 : ℝ))=(10001169663850443/10000000000000000 : ℝ) by norm_num, show 1+(16894911854787859/50000000000000000000 : ℝ)+(6968129379027361/50000000000000000000 : ℝ)=(2501193152061690761/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16894911854787859/50000000000000000000 : ℝ) ≤ ((9166946430290228793/9170000000000000000 : ℝ)+2*(243258546199/137550000000000 : ℝ)*(14097/100000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (9166946430290228793/9170000000000000000 : ℝ)+2*(243258546199/137550000000000 : ℝ)*(14097/100000 : ℝ)=(10001656180942841/10000000000000000 : ℝ) by norm_num, show 1+2*(16894911854787859/50000000000000000000 : ℝ)=(25016894911854787859/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9166946430290228793/9170000000000000000 : ℝ)*(X 1 0+X 2 0)+(243258546199/137550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (9166946430290228793/9170000000000000000 : ℝ)) (alpha := (243258546199/137550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9166946430290228793/9170000000000000000 : ℝ)*(X 0 1+X 2 1)+(243258546199/137550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (9166946430290228793/9170000000000000000 : ℝ)) (alpha := (243258546199/137550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9166946430290228793/9170000000000000000 : ℝ)*(X 0 2+X 1 2)+(243258546199/137550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (9166946430290228793/9170000000000000000 : ℝ)) (alpha := (243258546199/137550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2156857057/10000000000 : ℝ)*X 0 0+(2696478441/5000000000 : ℝ)*X 0 1+(1316446627/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672376683/5000000000 : ℝ)*X 1 0+(-2221359447/10000000000 : ℝ)*X 1 1+(5265786623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672376837/5000000000 : ℝ)*X 2 0+(2632893069/5000000000 : ℝ)*X 2 1+(-2221359679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180854227/5000000000 : ℝ)*X 0 0+(529564531/1250000000 : ℝ)*X 0 1+(898112493/2000000000 : ℝ)*X 0 2+(2180854227/5000000000 : ℝ)*X 1 0+(529564531/1250000000 : ℝ)*X 1 1+(898112493/2000000000 : ℝ)*X 1 2+(2180854227/5000000000 : ℝ)*X 2 0+(529564531/1250000000 : ℝ)*X 2 1+(898112493/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-269607787/1250000000 : ℝ)*X 0 0+(105322147/200000000 : ℝ)*X 0 1+(5392634619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656242373/5000000000 : ℝ)*X 1 0+(-1047255579/5000000000 : ℝ)*X 1 1+(674079323/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132812119/250000000 : ℝ)*X 2 0+(674079317/1250000000 : ℝ)*X 2 1+(-523627801/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361717787/10000000000 : ℝ)*X 0 0+(179596827/400000000 : ℝ)*X 0 1+(847432167/2000000000 : ℝ)*X 0 2+(4361717787/10000000000 : ℝ)*X 1 0+(179596827/400000000 : ℝ)*X 1 1+(847432167/2000000000 : ℝ)*X 1 2+(4361717787/10000000000 : ℝ)*X 2 0+(179596827/400000000 : ℝ)*X 2 1+(847432167/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121750289469251036212696467/14328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (524553391/100000000000000 : ℝ)*(base19) + (1000118037/100000000000000 : ℝ)*(base23) + (218163337/100000000000000 : ℝ)*(lower2) + (136426517/50000000000000 : ℝ)*(upper3) + (46029113/20000000000000 : ℝ)*(lower4) + (368744102902227/6250000000000 : ℝ)*(major0) + (368744102902227/6250000000000 : ℝ)*(major1) + (368744102902227/6250000000000 : ℝ)*(major2) + (1965870257674251/25000000000000 : ℝ)*(sp0) + (7863485702265667/100000000000000 : ℝ)*(sp1) + (3931742613350511/50000000000000 : ℝ)*(sp2) + (157452172020041/4000000000000 : ℝ)*(sp3) + (1039224411/20000000000000 : ℝ)*(sp4) + (5120577009/25000000000000 : ℝ)*(sp7) + (196816239140453/5000000000000 : ℝ)*(f.failure) + (7863486226819059/100000000000000 : ℝ)*(f.sum) + (13198236649639/2292500000000000000000000000 : ℝ)*base66 + (45883249340649573/8187500000000000000000000000000 : ℝ)*base67 + (29140986877899573/8187500000000000000000000000000 : ℝ)*base69 + (21148652590975427/8187500000000000000000000000000 : ℝ)*base72 + (11501120420823/4585000000000000000000000000 : ℝ)*base74 + (158183122578899573/8187500000000000000000000000000 : ℝ)*base75 + (38541745441149573/8187500000000000000000000000000 : ℝ)*base77 + (104777187415774573/8187500000000000000000000000000 : ℝ)*base79 + (6141770756483/4585000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6465123/500000000000000000000 : ℝ)*base90 + (6465123/500000000000000000000 : ℝ)*base92 + (6465123/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3679222515831957467500763127/458500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1588129723/100000000000000 : ℝ)*(base19) + (1581291423/100000000000000 : ℝ)*(base23) + (656807/50000000000000 : ℝ)*(upper2) + (138661427/100000000000000 : ℝ)*(upper3) + (1545383/800000000000 : ℝ)*(upper5) + (5929880514296187/100000000000000 : ℝ)*(major0) + (5929880514296187/100000000000000 : ℝ)*(major1) + (5929880514296187/100000000000000 : ℝ)*(major2) + (11142984389/25000000000000 : ℝ)*(sp1) + (39609709939/100000000000000 : ℝ)*(sp2) + (1975859303805039/25000000000000 : ℝ)*(sp4) + (1975847763788219/25000000000000 : ℝ)*(sp5) + (7903396024218793/100000000000000 : ℝ)*(sp6) + (494540443236207/12500000000000 : ℝ)*(sp7) + (494540443236207/12500000000000 : ℝ)*(f.failure) + (1975859303805039/25000000000000 : ℝ)*(f.sum) + (6300603108491/2292500000000000000000000000 : ℝ)*base65 + (237616050430244613/131000000000000000000000000000000 : ℝ)*base67 + (138932828613755387/131000000000000000000000000000000 : ℝ)*base70 + (825770698246244613/131000000000000000000000000000000 : ℝ)*base71 + (466129627979/2292500000000000000000000000 : ℝ)*base74 + (1544601041938244613/131000000000000000000000000000000 : ℝ)*base75 + (646907403947755387/131000000000000000000000000000000 : ℝ)*base78 + (4539745912500244613/131000000000000000000000000000000 : ℝ)*base79 + (5861516136047/4585000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7131063/1250000000000000000000 : ℝ)*base89 + (7131063/1250000000000000000000 : ℝ)*base91 + (7131063/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1163_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1163_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1163_s7_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-86275241/400000000 : ℝ)*x 0 + (269633581/500000000 : ℝ)*x 1 + (2633028023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86275241/400000000 : ℝ)^2089 ≤ (13108152272817/100000000000000 : ℝ)^1577 := by
    have hnat : (86275241 : ℕ)^2089*100000000000000^1577 ≤ 13108152272817^1577*400000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86275241 400000000 13108152272817 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269633581/500000000 : ℝ)^2089 ≤ (882591109077/2000000000000 : ℝ)^1577 := by
    have hnat : (269633581 : ℕ)^2089*2000000000000^1577 ≤ 882591109077^1577*500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269633581 500000000 882591109077 2000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633028023/5000000000 : ℝ)^2089 ≤ (42762292259009/100000000000000 : ℝ)^1577 := by
    have hnat : (2633028023 : ℕ)^2089*100000000000000^1577 ≤ 42762292259009^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633028023 5000000000 42762292259009 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86275241/400000000 : ℝ), (269633581/500000000 : ℝ), (2633028023/5000000000 : ℝ)] ![(13108152272817/100000000000000 : ℝ), (882591109077/2000000000000 : ℝ), (42762292259009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86275241/400000000 : ℝ)|^2089 ≤ (13108152272817/100000000000000 : ℝ)^1577
        have hw : |(-86275241/400000000 : ℝ)|=(86275241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269633581/500000000 : ℝ)|^2089 ≤ (882591109077/2000000000000 : ℝ)^1577
        have hw : |(269633581/500000000 : ℝ)|=(269633581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633028023/5000000000 : ℝ)|^2089 ≤ (42762292259009/100000000000000 : ℝ)^1577
        have hw : |(2633028023/5000000000 : ℝ)|=(2633028023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s7_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53446821/100000000 : ℝ)*x 0 + (-1110548839/5000000000 : ℝ)*x 1 + (658257003/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53446821/100000000 : ℝ)^2089 ≤ (43610098425489/100000000000000 : ℝ)^1577 := by
    have hnat : (53446821 : ℕ)^2089*100000000000000^1577 ≤ 43610098425489^1577*100000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53446821 100000000 43610098425489 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110548839/5000000000 : ℝ)^2089 ≤ (3406902384241/25000000000000 : ℝ)^1577 := by
    have hnat : (1110548839 : ℕ)^2089*25000000000000^1577 ≤ 3406902384241^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110548839 5000000000 3406902384241 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658257003/1250000000 : ℝ)^2089 ≤ (1069057300559/2500000000000 : ℝ)^1577 := by
    have hnat : (658257003 : ℕ)^2089*2500000000000^1577 ≤ 1069057300559^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658257003 1250000000 1069057300559 2500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53446821/100000000 : ℝ), (-1110548839/5000000000 : ℝ), (658257003/1250000000 : ℝ)] ![(43610098425489/100000000000000 : ℝ), (3406902384241/25000000000000 : ℝ), (1069057300559/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53446821/100000000 : ℝ)|^2089 ≤ (43610098425489/100000000000000 : ℝ)^1577
        have hw : |(53446821/100000000 : ℝ)|=(53446821/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1110548839/5000000000 : ℝ)|^2089 ≤ (3406902384241/25000000000000 : ℝ)^1577
        have hw : |(-1110548839/5000000000 : ℝ)|=(1110548839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658257003/1250000000 : ℝ)|^2089 ≤ (1069057300559/2500000000000 : ℝ)^1577
        have hw : |(658257003/1250000000 : ℝ)|=(658257003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s7_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344682093/10000000000 : ℝ)*x 0 + (329128503/625000000 : ℝ)*x 1 + (-2221097657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344682093/10000000000 : ℝ)^2089 ≤ (10902524587457/25000000000000 : ℝ)^1577 := by
    have hnat : (5344682093 : ℕ)^2089*25000000000000^1577 ≤ 10902524587457^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344682093 10000000000 10902524587457 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329128503/625000000 : ℝ)^2089 ≤ (42762292280523/100000000000000 : ℝ)^1577 := by
    have hnat : (329128503 : ℕ)^2089*100000000000000^1577 ≤ 42762292280523^1577*625000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329128503 625000000 42762292280523 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2221097657/10000000000 : ℝ)^2089 ≤ (6813804683143/50000000000000 : ℝ)^1577 := by
    have hnat : (2221097657 : ℕ)^2089*50000000000000^1577 ≤ 6813804683143^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221097657 10000000000 6813804683143 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344682093/10000000000 : ℝ), (329128503/625000000 : ℝ), (-2221097657/10000000000 : ℝ)] ![(10902524587457/25000000000000 : ℝ), (42762292280523/100000000000000 : ℝ), (6813804683143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344682093/10000000000 : ℝ)|^2089 ≤ (10902524587457/25000000000000 : ℝ)^1577
        have hw : |(5344682093/10000000000 : ℝ)|=(5344682093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329128503/625000000 : ℝ)|^2089 ≤ (42762292280523/100000000000000 : ℝ)^1577
        have hw : |(329128503/625000000 : ℝ)|=(329128503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2221097657/10000000000 : ℝ)|^2089 ≤ (6813804683143/50000000000000 : ℝ)^1577
        have hw : |(-2221097657/10000000000 : ℝ)|=(2221097657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s7_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (545215273/1250000000 : ℝ)*x 0 + (529633689/1250000000 : ℝ)*x 1 + (224500297/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545215273/1250000000 : ℝ)^2089 ≤ (33317070808409/100000000000000 : ℝ)^1577 := by
    have hnat : (545215273 : ℕ)^2089*100000000000000^1577 ≤ 33317070808409^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545215273 1250000000 33317070808409 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529633689/1250000000 : ℝ)^2089 ≤ (32061664051559/100000000000000 : ℝ)^1577 := by
    have hnat : (529633689 : ℕ)^2089*100000000000000^1577 ≤ 32061664051559^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529633689 1250000000 32061664051559 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224500297/500000000 : ℝ)^2089 ≤ (34621265127703/100000000000000 : ℝ)^1577 := by
    have hnat : (224500297 : ℕ)^2089*100000000000000^1577 ≤ 34621265127703^1577*500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224500297 500000000 34621265127703 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545215273/1250000000 : ℝ), (529633689/1250000000 : ℝ), (224500297/500000000 : ℝ)] ![(33317070808409/100000000000000 : ℝ), (32061664051559/100000000000000 : ℝ), (34621265127703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545215273/1250000000 : ℝ)|^2089 ≤ (33317070808409/100000000000000 : ℝ)^1577
        have hw : |(545215273/1250000000 : ℝ)|=(545215273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529633689/1250000000 : ℝ)|^2089 ≤ (32061664051559/100000000000000 : ℝ)^1577
        have hw : |(529633689/1250000000 : ℝ)|=(529633689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224500297/500000000 : ℝ)|^2089 ≤ (34621265127703/100000000000000 : ℝ)^1577
        have hw : |(224500297/500000000 : ℝ)|=(224500297/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s7_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-43137717/200000000 : ℝ)*x 0 + (10532749/20000000 : ℝ)*x 1 + (5392352023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43137717/200000000 : ℝ)^2089 ≤ (655409555821/5000000000000 : ℝ)^1577 := by
    have hnat : (43137717 : ℕ)^2089*5000000000000^1577 ≤ 655409555821^1577*200000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43137717 200000000 655409555821 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10532749/20000000 : ℝ)^2089 ≤ (5345714728993/12500000000000 : ℝ)^1577 := by
    have hnat : (10532749 : ℕ)^2089*12500000000000^1577 ≤ 5345714728993^1577*20000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10532749 20000000 5345714728993 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392352023/10000000000 : ℝ)^2089 ≤ (44126091031437/100000000000000 : ℝ)^1577 := by
    have hnat : (5392352023 : ℕ)^2089*100000000000000^1577 ≤ 44126091031437^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392352023 10000000000 44126091031437 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43137717/200000000 : ℝ), (10532749/20000000 : ℝ), (5392352023/10000000000 : ℝ)] ![(655409555821/5000000000000 : ℝ), (5345714728993/12500000000000 : ℝ), (44126091031437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43137717/200000000 : ℝ)|^2089 ≤ (655409555821/5000000000000 : ℝ)^1577
        have hw : |(-43137717/200000000 : ℝ)|=(43137717/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10532749/20000000 : ℝ)|^2089 ≤ (5345714728993/12500000000000 : ℝ)^1577
        have hw : |(10532749/20000000 : ℝ)|=(10532749/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392352023/10000000000 : ℝ)|^2089 ≤ (44126091031437/100000000000000 : ℝ)^1577
        have hw : |(5392352023/10000000000 : ℝ)|=(5392352023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s7_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062510779/2000000000 : ℝ)*x 0 + (-2094801681/10000000000 : ℝ)*x 1 + (337022003/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062510779/2000000000 : ℝ)^2089 ≤ (5407896855779/12500000000000 : ℝ)^1577 := by
    have hnat : (1062510779 : ℕ)^2089*12500000000000^1577 ≤ 5407896855779^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062510779 2000000000 5407896855779 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094801681/10000000000 : ℝ)^2089 ≤ (504429353333/4000000000000 : ℝ)^1577 := by
    have hnat : (2094801681 : ℕ)^2089*4000000000000^1577 ≤ 504429353333^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094801681 10000000000 504429353333 4000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337022003/625000000 : ℝ)^2089 ≤ (22063045651217/50000000000000 : ℝ)^1577 := by
    have hnat : (337022003 : ℕ)^2089*50000000000000^1577 ≤ 22063045651217^1577*625000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337022003 625000000 22063045651217 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062510779/2000000000 : ℝ), (-2094801681/10000000000 : ℝ), (337022003/625000000 : ℝ)] ![(5407896855779/12500000000000 : ℝ), (504429353333/4000000000000 : ℝ), (22063045651217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062510779/2000000000 : ℝ)|^2089 ≤ (5407896855779/12500000000000 : ℝ)^1577
        have hw : |(1062510779/2000000000 : ℝ)|=(1062510779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094801681/10000000000 : ℝ)|^2089 ≤ (504429353333/4000000000000 : ℝ)^1577
        have hw : |(-2094801681/10000000000 : ℝ)|=(2094801681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337022003/625000000 : ℝ)|^2089 ≤ (22063045651217/50000000000000 : ℝ)^1577
        have hw : |(337022003/625000000 : ℝ)|=(337022003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s7_6 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531255389/1000000000 : ℝ)*x 0 + (5392352059/10000000000 : ℝ)*x 1 + (-2094801673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531255389/1000000000 : ℝ)^2089 ≤ (21631587396147/50000000000000 : ℝ)^1577 := by
    have hnat : (531255389 : ℕ)^2089*50000000000000^1577 ≤ 21631587396147^1577*1000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531255389 1000000000 21631587396147 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392352059/10000000000 : ℝ)^2089 ≤ (5515761427709/12500000000000 : ℝ)^1577 := by
    have hnat : (5392352059 : ℕ)^2089*12500000000000^1577 ≤ 5515761427709^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392352059 10000000000 5515761427709 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2094801673/10000000000 : ℝ)^2089 ≤ (12610733769529/100000000000000 : ℝ)^1577 := by
    have hnat : (2094801673 : ℕ)^2089*100000000000000^1577 ≤ 12610733769529^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094801673 10000000000 12610733769529 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531255389/1000000000 : ℝ), (5392352059/10000000000 : ℝ), (-2094801673/10000000000 : ℝ)] ![(21631587396147/50000000000000 : ℝ), (5515761427709/12500000000000 : ℝ), (12610733769529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531255389/1000000000 : ℝ)|^2089 ≤ (21631587396147/50000000000000 : ℝ)^1577
        have hw : |(531255389/1000000000 : ℝ)|=(531255389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392352059/10000000000 : ℝ)|^2089 ≤ (5515761427709/12500000000000 : ℝ)^1577
        have hw : |(5392352059/10000000000 : ℝ)|=(5392352059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2094801673/10000000000 : ℝ)|^2089 ≤ (12610733769529/100000000000000 : ℝ)^1577
        have hw : |(-2094801673/10000000000 : ℝ)|=(2094801673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s7_7 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2180865923/5000000000 : ℝ)*x 0 + (2244684899/5000000000 : ℝ)*x 1 + (4237707959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180865923/5000000000 : ℝ)^2089 ≤ (33317168573261/100000000000000 : ℝ)^1577 := by
    have hnat : (2180865923 : ℕ)^2089*100000000000000^1577 ≤ 33317168573261^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180865923 5000000000 33317168573261 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244684899/5000000000 : ℝ)^2089 ≤ (34614767619359/100000000000000 : ℝ)^1577 := by
    have hnat : (2244684899 : ℕ)^2089*100000000000000^1577 ≤ 34614767619359^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244684899 5000000000 34614767619359 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237707959/10000000000 : ℝ)^2089 ≤ (1603403189843/5000000000000 : ℝ)^1577 := by
    have hnat : (4237707959 : ℕ)^2089*5000000000000^1577 ≤ 1603403189843^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237707959 10000000000 1603403189843 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180865923/5000000000 : ℝ), (2244684899/5000000000 : ℝ), (4237707959/10000000000 : ℝ)] ![(33317168573261/100000000000000 : ℝ), (34614767619359/100000000000000 : ℝ), (1603403189843/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180865923/5000000000 : ℝ)|^2089 ≤ (33317168573261/100000000000000 : ℝ)^1577
        have hw : |(2180865923/5000000000 : ℝ)|=(2180865923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244684899/5000000000 : ℝ)|^2089 ≤ (34614767619359/100000000000000 : ℝ)^1577
        have hw : |(2244684899/5000000000 : ℝ)|=(2244684899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237707959/10000000000 : ℝ)|^2089 ≤ (1603403189843/5000000000000 : ℝ)^1577
        have hw : |(4237707959/10000000000 : ℝ)|=(4237707959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (569/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7031/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5687/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5687/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5687/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5687/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5687/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5687/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5687/50000 : ℝ) ^ (8355/2048 : ℝ) ≤ (3519274845503251/25000000000000000000 : ℝ) := by
    have hpowers : (5687/50000 : ℝ)^8355 ≤ (3519274845503251/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5687 : ℕ)^8355*25000000000000000000^2048 ≤ 3519274845503251^2048*50000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5687 50000 3519274845503251 25000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5687/50000 : ℝ)) (X := (3519274845503251/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3517/25000 : ℝ) ^ (8355/2048 : ℝ) ≤ (4188392740482931/12500000000000000000 : ℝ) := by
    have hpowers : (3517/25000 : ℝ)^8355 ≤ (4188392740482931/12500000000000000000 : ℝ)^2048 := by
      have hnat : (3517 : ℕ)^8355*12500000000000000000^2048 ≤ 4188392740482931^2048*25000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3517 25000 4188392740482931 12500000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3517/25000 : ℝ)) (X := (4188392740482931/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503519274845503251/12500000000000000000 : ℝ) ≤ (10000690049944571/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (12503519274845503251/12500000000000000000 : ℝ)^2048 ≤ (10000690049944571/10000000000000000 : ℝ)^8355 := by
      have hnat : (12503519274845503251 : ℕ)^2048*10000000000000000^8355 ≤ 10000690049944571^8355*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503519274845503251 12500000000000000000 10000690049944571 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690049944571/10000000000000000 : ℝ)) (X := (12503519274845503251/12500000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011896060326469113/25000000000000000000 : ℝ) ≤ (1000116618825209/1000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (25011896060326469113/25000000000000000000 : ℝ)^2048 ≤ (1000116618825209/1000000000000000 : ℝ)^8355 := by
      have hnat : (25011896060326469113 : ℕ)^2048*1000000000000000^8355 ≤ 1000116618825209^8355*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011896060326469113 25000000000000000000 1000116618825209 1000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000116618825209/1000000000000000 : ℝ)) (X := (25011896060326469113/25000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254188392740482931/6250000000000000000 : ℝ) ≤ (10001642326559609/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (6254188392740482931/6250000000000000000 : ℝ)^2048 ≤ (10001642326559609/10000000000000000 : ℝ)^8355 := by
      have hnat : (6254188392740482931 : ℕ)^2048*10000000000000000^8355 ≤ 10001642326559609^8355*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254188392740482931 6250000000000000000 10001642326559609 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001642326559609/10000000000000000 : ℝ)) (X := (6254188392740482931/6250000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3519274845503251/25000000000000000000 : ℝ) ≤ ((4488504633388538677/4490000000000000000 : ℝ)+2*(158712769173/89800000000000 : ℝ)*(5687/50000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (4488504633388538677/4490000000000000000 : ℝ)+2*(158712769173/89800000000000 : ℝ)*(5687/50000 : ℝ)=(10000690049944571/10000000000000000 : ℝ) by norm_num, show 1+2*(3519274845503251/25000000000000000000 : ℝ)=(12503519274845503251/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4188392740482931/12500000000000000000 : ℝ)+(3519274845503251/25000000000000000000 : ℝ) ≤ ((4488504633388538677/4490000000000000000 : ℝ)+(158712769173/89800000000000 : ℝ)*((3517/25000 : ℝ)+(5687/50000 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (4488504633388538677/4490000000000000000 : ℝ)+(158712769173/89800000000000 : ℝ)*((3517/25000 : ℝ)+(5687/50000 : ℝ))=(1000116618825209/1000000000000000 : ℝ) by norm_num, show 1+(4188392740482931/12500000000000000000 : ℝ)+(3519274845503251/25000000000000000000 : ℝ)=(25011896060326469113/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4188392740482931/12500000000000000000 : ℝ) ≤ ((4488504633388538677/4490000000000000000 : ℝ)+2*(158712769173/89800000000000 : ℝ)*(3517/25000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (4488504633388538677/4490000000000000000 : ℝ)+2*(158712769173/89800000000000 : ℝ)*(3517/25000 : ℝ)=(10001642326559609/10000000000000000 : ℝ) by norm_num, show 1+2*(4188392740482931/12500000000000000000 : ℝ)=(6254188392740482931/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4488504633388538677/4490000000000000000 : ℝ)*(X 1 0+X 2 0)+(158712769173/89800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (4488504633388538677/4490000000000000000 : ℝ)) (alpha := (158712769173/89800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4488504633388538677/4490000000000000000 : ℝ)*(X 0 1+X 2 1)+(158712769173/89800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (4488504633388538677/4490000000000000000 : ℝ)) (alpha := (158712769173/89800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4488504633388538677/4490000000000000000 : ℝ)*(X 0 2+X 1 2)+(158712769173/89800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (4488504633388538677/4490000000000000000 : ℝ)) (alpha := (158712769173/89800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-86275241/400000000 : ℝ)*X 0 0+(269633581/500000000 : ℝ)*X 0 1+(2633028023/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53446821/100000000 : ℝ)*X 1 0+(-1110548839/5000000000 : ℝ)*X 1 1+(658257003/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344682093/10000000000 : ℝ)*X 2 0+(329128503/625000000 : ℝ)*X 2 1+(-2221097657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545215273/1250000000 : ℝ)*X 0 0+(529633689/1250000000 : ℝ)*X 0 1+(224500297/500000000 : ℝ)*X 0 2+(545215273/1250000000 : ℝ)*X 1 0+(529633689/1250000000 : ℝ)*X 1 1+(224500297/500000000 : ℝ)*X 1 2+(545215273/1250000000 : ℝ)*X 2 0+(529633689/1250000000 : ℝ)*X 2 1+(224500297/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-43137717/200000000 : ℝ)*X 0 0+(10532749/20000000 : ℝ)*X 0 1+(5392352023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062510779/2000000000 : ℝ)*X 1 0+(-2094801681/10000000000 : ℝ)*X 1 1+(337022003/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531255389/1000000000 : ℝ)*X 2 0+(5392352059/10000000000 : ℝ)*X 2 1+(-2094801673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180865923/5000000000 : ℝ)*X 0 0+(2244684899/5000000000 : ℝ)*X 0 1+(4237707959/10000000000 : ℝ)*X 0 2+(2180865923/5000000000 : ℝ)*X 1 0+(2244684899/5000000000 : ℝ)*X 1 1+(4237707959/10000000000 : ℝ)*X 1 2+(2180865923/5000000000 : ℝ)*X 2 0+(2244684899/5000000000 : ℝ)*X 2 1+(4237707959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (490764834840836455793085453/112250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (842963379/100000000000000 : ℝ)*(base19) + (756421903/100000000000000 : ℝ)*(base23) + (4072509/10000000000000 : ℝ)*(lower2) + (19670033/20000000000000 : ℝ)*(upper3) + (37528061/50000000000000 : ℝ)*(upper5) + (5925776489535563/100000000000000 : ℝ)*(major0) + (5925776489535563/100000000000000 : ℝ)*(major1) + (5925776489535563/100000000000000 : ℝ)*(major2) + (7897944994898519/100000000000000 : ℝ)*(sp0) + (7897966585622737/100000000000000 : ℝ)*(sp1) + (7897966672164213/100000000000000 : ℝ)*(sp2) + (15814294241499/400000000000 : ℝ)*(sp3) + (22433687597/100000000000000 : ℝ)*(sp4) + (11844374587/100000000000000 : ℝ)*(sp7) + (494198175593667/12500000000000 : ℝ)*(f.failure) + (7897967428586117/100000000000000 : ℝ)*(f.sum) + (2302589225331/4490000000000000000000000000 : ℝ)*base66 + (2566285254031579849/449000000000000000000000000000000 : ℝ)*base68 + (5141055473599579849/449000000000000000000000000000000 : ℝ)*base70 + (526840415635579849/449000000000000000000000000000000 : ℝ)*base72 + (4506524676799/4490000000000000000000000000 : ℝ)*base73 + (2132357002133420151/449000000000000000000000000000000 : ℝ)*base75 + (5456694334576579849/449000000000000000000000000000000 : ℝ)*base78 + (5762897175887579849/449000000000000000000000000000000 : ℝ)*base80 + (4693922675319/4490000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9995797/1250000000000000000000 : ℝ)*base90 + (9995797/1250000000000000000000 : ℝ)*base92 + (9995797/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (467278225208462824520383029/56125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (134963723/10000000000000 : ℝ)*(base19) + (1521102283/100000000000000 : ℝ)*(base23) + (41640257/25000000000000 : ℝ)*(upper3) + (313711/400000000000 : ℝ)*(lower4) + (77646453/50000000000000 : ℝ)*(upper5) + (1488938408766247/25000000000000 : ℝ)*(major0) + (1488938408766247/25000000000000 : ℝ)*(major1) + (1488938408766247/25000000000000 : ℝ)*(major2) + (37621857191/100000000000000 : ℝ)*(sp1) + (42798912929/100000000000000 : ℝ)*(sp2) + (992240163144081/12500000000000 : ℝ)*(sp4) + (3968941166829113/50000000000000 : ℝ)*(sp5) + (1984469246284359/25000000000000 : ℝ)*(sp6) + (1986792843727491/50000000000000 : ℝ)*(sp7) + (1986792843727491/50000000000000 : ℝ)*(f.failure) + (992240163144081/12500000000000 : ℝ)*(f.sum) + (3318156600161/1122500000000000000000000000 : ℝ)*base65 + (949402692357185219/112250000000000000000000000000000 : ℝ)*base67 + (1554239478933685219/112250000000000000000000000000000 : ℝ)*base69 + (972961890058685219/112250000000000000000000000000000 : ℝ)*base71 + (2337173250811/1122500000000000000000000000 : ℝ)*base73 + (2983203471665685219/112250000000000000000000000000000 : ℝ)*base75 + (1683522903787935219/112250000000000000000000000000000 : ℝ)*base77 + (2188221831636185219/112250000000000000000000000000000 : ℝ)*base79 + (9466274923997/2245000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (36404981/5000000000000000000000 : ℝ)*base90 + (36404981/5000000000000000000000 : ℝ)*base92 + (36404981/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1163_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1163_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1163_s8_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2156885301/10000000000 : ℝ)*x 0 + (5392612499/10000000000 : ℝ)*x 1 + (210644497/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156885301/10000000000 : ℝ)^2089 ≤ (13108186696701/100000000000000 : ℝ)^1577 := by
    have hnat : (2156885301 : ℕ)^2089*100000000000000^1577 ≤ 13108186696701^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156885301 10000000000 13108186696701 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392612499/10000000000 : ℝ)^2089 ≤ (44128914578863/100000000000000 : ℝ)^1577 := by
    have hnat : (5392612499 : ℕ)^2089*100000000000000^1577 ≤ 44128914578863^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392612499 10000000000 44128914578863 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210644497/400000000 : ℝ)^2089 ≤ (10690724679127/25000000000000 : ℝ)^1577 := by
    have hnat : (210644497 : ℕ)^2089*25000000000000^1577 ≤ 10690724679127^1577*400000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210644497 400000000 10690724679127 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2156885301/10000000000 : ℝ), (5392612499/10000000000 : ℝ), (210644497/400000000 : ℝ)] ![(13108186696701/100000000000000 : ℝ), (44128914578863/100000000000000 : ℝ), (10690724679127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2156885301/10000000000 : ℝ)|^2089 ≤ (13108186696701/100000000000000 : ℝ)^1577
        have hw : |(-2156885301/10000000000 : ℝ)|=(2156885301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392612499/10000000000 : ℝ)|^2089 ≤ (44128914578863/100000000000000 : ℝ)^1577
        have hw : |(5392612499/10000000000 : ℝ)|=(5392612499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210644497/400000000 : ℝ)|^2089 ≤ (10690724679127/25000000000000 : ℝ)^1577
        have hw : |(210644497/400000000 : ℝ)|=(210644497/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s8_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344667447/10000000000 : ℝ)*x 0 + (-2221042493/10000000000 : ℝ)*x 1 + (1316528111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344667447/10000000000 : ℝ)^2089 ≤ (10902485011559/25000000000000 : ℝ)^1577 := by
    have hnat : (5344667447 : ℕ)^2089*25000000000000^1577 ≤ 10902485011559^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344667447 10000000000 10902485011559 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2221042493/10000000000 : ℝ)^2089 ≤ (2725432204167/20000000000000 : ℝ)^1577 := by
    have hnat : (2221042493 : ℕ)^2089*20000000000000^1577 ≤ 2725432204167^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221042493 10000000000 2725432204167 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316528111/2500000000 : ℝ)^2089 ≤ (42762898920887/100000000000000 : ℝ)^1577 := by
    have hnat : (1316528111 : ℕ)^2089*100000000000000^1577 ≤ 42762898920887^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316528111 2500000000 42762898920887 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344667447/10000000000 : ℝ), (-2221042493/10000000000 : ℝ), (1316528111/2500000000 : ℝ)] ![(10902485011559/25000000000000 : ℝ), (2725432204167/20000000000000 : ℝ), (42762898920887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344667447/10000000000 : ℝ)|^2089 ≤ (10902485011559/25000000000000 : ℝ)^1577
        have hw : |(5344667447/10000000000 : ℝ)|=(5344667447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2221042493/10000000000 : ℝ)|^2089 ≤ (2725432204167/20000000000000 : ℝ)^1577
        have hw : |(-2221042493/10000000000 : ℝ)|=(2221042493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316528111/2500000000 : ℝ)|^2089 ≤ (42762898920887/100000000000000 : ℝ)^1577
        have hw : |(1316528111/2500000000 : ℝ)|=(1316528111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s8_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66808343/125000000 : ℝ)*x 0 + (263305623/500000000 : ℝ)*x 1 + (-27763031/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66808343/125000000 : ℝ)^2089 ≤ (1744397598823/4000000000000 : ℝ)^1577 := by
    have hnat : (66808343 : ℕ)^2089*4000000000000^1577 ≤ 1744397598823^1577*125000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66808343 125000000 1744397598823 4000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263305623/500000000 : ℝ)^2089 ≤ (10690724773249/25000000000000 : ℝ)^1577 := by
    have hnat : (263305623 : ℕ)^2089*25000000000000^1577 ≤ 10690724773249^1577*500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263305623 500000000 10690724773249 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27763031/125000000 : ℝ)^2089 ≤ (6813580457589/50000000000000 : ℝ)^1577 := by
    have hnat : (27763031 : ℕ)^2089*50000000000000^1577 ≤ 6813580457589^1577*125000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27763031 125000000 6813580457589 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66808343/125000000 : ℝ), (263305623/500000000 : ℝ), (-27763031/125000000 : ℝ)] ![(1744397598823/4000000000000 : ℝ), (10690724773249/25000000000000 : ℝ), (6813580457589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66808343/125000000 : ℝ)|^2089 ≤ (1744397598823/4000000000000 : ℝ)^1577
        have hw : |(66808343/125000000 : ℝ)|=(66808343/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263305623/500000000 : ℝ)|^2089 ≤ (10690724773249/25000000000000 : ℝ)^1577
        have hw : |(263305623/500000000 : ℝ)|=(263305623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27763031/125000000 : ℝ)|^2089 ≤ (6813580457589/50000000000000 : ℝ)^1577
        have hw : |(-27763031/125000000 : ℝ)|=(27763031/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s8_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4361725133/10000000000 : ℝ)*x 0 + (2118592261/5000000000 : ℝ)*x 1 + (4489890151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361725133/10000000000 : ℝ)^2089 ≤ (33317100647829/100000000000000 : ℝ)^1577 := by
    have hnat : (4361725133 : ℕ)^2089*100000000000000^1577 ≤ 33317100647829^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361725133 10000000000 33317100647829 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118592261/5000000000 : ℝ)^2089 ≤ (16031408440069/50000000000000 : ℝ)^1577 := by
    have hnat : (2118592261 : ℕ)^2089*50000000000000^1577 ≤ 16031408440069^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118592261 5000000000 16031408440069 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489890151/10000000000 : ℝ)^2089 ≤ (34620082444987/100000000000000 : ℝ)^1577 := by
    have hnat : (4489890151 : ℕ)^2089*100000000000000^1577 ≤ 34620082444987^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489890151 10000000000 34620082444987 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361725133/10000000000 : ℝ), (2118592261/5000000000 : ℝ), (4489890151/10000000000 : ℝ)] ![(33317100647829/100000000000000 : ℝ), (16031408440069/50000000000000 : ℝ), (34620082444987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361725133/10000000000 : ℝ)|^2089 ≤ (33317100647829/100000000000000 : ℝ)^1577
        have hw : |(4361725133/10000000000 : ℝ)|=(4361725133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118592261/5000000000 : ℝ)|^2089 ≤ (16031408440069/50000000000000 : ℝ)^1577
        have hw : |(2118592261/5000000000 : ℝ)|=(2118592261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489890151/10000000000 : ℝ)|^2089 ≤ (34620082444987/100000000000000 : ℝ)^1577
        have hw : |(4489890151/10000000000 : ℝ)|=(4489890151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s8_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-269611303/1250000000 : ℝ)*x 0 + (1316607617/2500000000 : ℝ)*x 1 + (2696146543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269611303/1250000000 : ℝ)^2089 ≤ (13108227939377/100000000000000 : ℝ)^1577 := by
    have hnat : (269611303 : ℕ)^2089*100000000000000^1577 ≤ 13108227939377^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269611303 1250000000 13108227939377 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316607617/2500000000 : ℝ)^2089 ≤ (42766319880211/100000000000000 : ℝ)^1577 := by
    have hnat : (1316607617 : ℕ)^2089*100000000000000^1577 ≤ 42766319880211^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316607617 2500000000 42766319880211 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696146543/5000000000 : ℝ)^2089 ≤ (44125452163309/100000000000000 : ℝ)^1577 := by
    have hnat : (2696146543 : ℕ)^2089*100000000000000^1577 ≤ 44125452163309^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696146543 5000000000 44125452163309 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269611303/1250000000 : ℝ), (1316607617/2500000000 : ℝ), (2696146543/5000000000 : ℝ)] ![(13108227939377/100000000000000 : ℝ), (42766319880211/100000000000000 : ℝ), (44125452163309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269611303/1250000000 : ℝ)|^2089 ≤ (13108227939377/100000000000000 : ℝ)^1577
        have hw : |(-269611303/1250000000 : ℝ)|=(269611303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316607617/2500000000 : ℝ)|^2089 ≤ (42766319880211/100000000000000 : ℝ)^1577
        have hw : |(1316607617/2500000000 : ℝ)|=(1316607617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696146543/5000000000 : ℝ)|^2089 ≤ (44125452163309/100000000000000 : ℝ)^1577
        have hw : |(2696146543/5000000000 : ℝ)|=(2696146543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s8_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312568661/10000000000 : ℝ)*x 0 + (-1047430643/5000000000 : ℝ)*x 1 + (1078458701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312568661/10000000000 : ℝ)^2089 ≤ (21631667067443/50000000000000 : ℝ)^1577 := by
    have hnat : (5312568661 : ℕ)^2089*50000000000000^1577 ≤ 21631667067443^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312568661 10000000000 21631667067443 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047430643/5000000000 : ℝ)^2089 ≤ (1576401144549/12500000000000 : ℝ)^1577 := by
    have hnat : (1047430643 : ℕ)^2089*12500000000000^1577 ≤ 1576401144549^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047430643 5000000000 1576401144549 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078458701/2000000000 : ℝ)^2089 ≤ (22062728352599/50000000000000 : ℝ)^1577 := by
    have hnat : (1078458701 : ℕ)^2089*50000000000000^1577 ≤ 22062728352599^1577*2000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078458701 2000000000 22062728352599 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312568661/10000000000 : ℝ), (-1047430643/5000000000 : ℝ), (1078458701/2000000000 : ℝ)] ![(21631667067443/50000000000000 : ℝ), (1576401144549/12500000000000 : ℝ), (22062728352599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312568661/10000000000 : ℝ)|^2089 ≤ (21631667067443/50000000000000 : ℝ)^1577
        have hw : |(5312568661/10000000000 : ℝ)|=(5312568661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1047430643/5000000000 : ℝ)|^2089 ≤ (1576401144549/12500000000000 : ℝ)^1577
        have hw : |(-1047430643/5000000000 : ℝ)|=(1047430643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078458701/2000000000 : ℝ)|^2089 ≤ (22062728352599/50000000000000 : ℝ)^1577
        have hw : |(1078458701/2000000000 : ℝ)|=(1078458701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s8_6 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656284399/5000000000 : ℝ)*x 0 + (2696146643/5000000000 : ℝ)*x 1 + (-1047430699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656284399/5000000000 : ℝ)^2089 ≤ (21631667806389/50000000000000 : ℝ)^1577 := by
    have hnat : (2656284399 : ℕ)^2089*50000000000000^1577 ≤ 21631667806389^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656284399 5000000000 21631667806389 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696146643/5000000000 : ℝ)^2089 ≤ (1765018173251/4000000000000 : ℝ)^1577 := by
    have hnat : (2696146643 : ℕ)^2089*4000000000000^1577 ≤ 1765018173251^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696146643 5000000000 1765018173251 4000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047430699/5000000000 : ℝ)^2089 ≤ (6305605024773/50000000000000 : ℝ)^1577 := by
    have hnat : (1047430699 : ℕ)^2089*50000000000000^1577 ≤ 6305605024773^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047430699 5000000000 6305605024773 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656284399/5000000000 : ℝ), (2696146643/5000000000 : ℝ), (-1047430699/5000000000 : ℝ)] ![(21631667806389/50000000000000 : ℝ), (1765018173251/4000000000000 : ℝ), (6305605024773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656284399/5000000000 : ℝ)|^2089 ≤ (21631667806389/50000000000000 : ℝ)^1577
        have hw : |(2656284399/5000000000 : ℝ)|=(2656284399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696146643/5000000000 : ℝ)|^2089 ≤ (1765018173251/4000000000000 : ℝ)^1577
        have hw : |(2696146643/5000000000 : ℝ)|=(2696146643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047430699/5000000000 : ℝ)|^2089 ≤ (6305605024773/50000000000000 : ℝ)^1577
        have hw : |(-1047430699/5000000000 : ℝ)|=(1047430699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s8_7 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (174469383/400000000 : ℝ)*x 0 + (1122313839/2500000000 : ℝ)*x 1 + (4237821809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174469383/400000000 : ℝ)^2089 ≤ (16658598093317/50000000000000 : ℝ)^1577 := by
    have hnat : (174469383 : ℕ)^2089*50000000000000^1577 ≤ 16658598093317^1577*400000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174469383 400000000 16658598093317 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122313839/2500000000 : ℝ)^2089 ≤ (34613598748777/100000000000000 : ℝ)^1577 := by
    have hnat : (1122313839 : ℕ)^2089*100000000000000^1577 ≤ 34613598748777^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122313839 2500000000 34613598748777 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237821809/10000000000 : ℝ)^2089 ≤ (8017301263423/25000000000000 : ℝ)^1577 := by
    have hnat : (4237821809 : ℕ)^2089*25000000000000^1577 ≤ 8017301263423^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237821809 10000000000 8017301263423 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174469383/400000000 : ℝ), (1122313839/2500000000 : ℝ), (4237821809/10000000000 : ℝ)] ![(16658598093317/50000000000000 : ℝ), (34613598748777/100000000000000 : ℝ), (8017301263423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174469383/400000000 : ℝ)|^2089 ≤ (16658598093317/50000000000000 : ℝ)^1577
        have hw : |(174469383/400000000 : ℝ)|=(174469383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122313839/2500000000 : ℝ)|^2089 ≤ (34613598748777/100000000000000 : ℝ)^1577
        have hw : |(1122313839/2500000000 : ℝ)|=(1122313839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237821809/10000000000 : ℝ)|^2089 ≤ (8017301263423/25000000000000 : ℝ)^1577
        have hw : |(4237821809/10000000000 : ℝ)|=(4237821809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11381/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14061/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (569/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (569/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (569/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (569/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (569/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (569/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (569/5000 : ℝ) ^ (8355/2048 : ℝ) ≤ (881713673233993/6250000000000000000 : ℝ) := by
    have hpowers : (569/5000 : ℝ)^8355 ≤ (881713673233993/6250000000000000000 : ℝ)^2048 := by
      have hnat : (569 : ℕ)^8355*6250000000000000000^2048 ≤ 881713673233993^2048*5000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        569 5000 881713673233993 6250000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (569/5000 : ℝ)) (X := (881713673233993/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7031/50000 : ℝ) ^ (8355/2048 : ℝ) ≤ (6689775926583349/20000000000000000000 : ℝ) := by
    have hpowers : (7031/50000 : ℝ)^8355 ≤ (6689775926583349/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7031 : ℕ)^8355*20000000000000000000^2048 ≤ 6689775926583349^2048*50000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 50000 6689775926583349 20000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/50000 : ℝ)) (X := (6689775926583349/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125881713673233993/3125000000000000000 : ℝ) ≤ (5000345768011213/5000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (3125881713673233993/3125000000000000000 : ℝ)^2048 ≤ (5000345768011213/5000000000000000 : ℝ)^8355 := by
      have hnat : (3125881713673233993 : ℕ)^2048*5000000000000000^8355 ≤ 5000345768011213^8355*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125881713673233993 3125000000000000000 5000345768011213 5000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000345768011213/5000000000000000 : ℝ)) (X := (3125881713673233993/3125000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047556298404660633/100000000000000000000 : ℝ) ≤ (10001165503554063/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (100047556298404660633/100000000000000000000 : ℝ)^2048 ≤ (10001165503554063/10000000000000000 : ℝ)^8355 := by
      have hnat : (100047556298404660633 : ℕ)^2048*10000000000000000^8355 ≤ 10001165503554063^8355*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047556298404660633 100000000000000000000 10001165503554063 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001165503554063/10000000000000000 : ℝ)) (X := (100047556298404660633/100000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006689775926583349/10000000000000000000 : ℝ) ≤ (100016394710857/100000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (10006689775926583349/10000000000000000000 : ℝ)^2048 ≤ (100016394710857/100000000000000 : ℝ)^8355 := by
      have hnat : (10006689775926583349 : ℕ)^2048*100000000000000^8355 ≤ 100016394710857^8355*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006689775926583349 10000000000000000000 100016394710857 100000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100016394710857/100000000000000 : ℝ)) (X := (10006689775926583349/10000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(881713673233993/6250000000000000000 : ℝ) ≤ ((6702766799648022103/6705000000000000000 : ℝ)+2*(473967531637/268200000000000 : ℝ)*(569/5000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (6702766799648022103/6705000000000000000 : ℝ)+2*(473967531637/268200000000000 : ℝ)*(569/5000 : ℝ)=(5000345768011213/5000000000000000 : ℝ) by norm_num, show 1+2*(881713673233993/6250000000000000000 : ℝ)=(3125881713673233993/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6689775926583349/20000000000000000000 : ℝ)+(881713673233993/6250000000000000000 : ℝ) ≤ ((6702766799648022103/6705000000000000000 : ℝ)+(473967531637/268200000000000 : ℝ)*((7031/50000 : ℝ)+(569/5000 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (6702766799648022103/6705000000000000000 : ℝ)+(473967531637/268200000000000 : ℝ)*((7031/50000 : ℝ)+(569/5000 : ℝ))=(10001165503554063/10000000000000000 : ℝ) by norm_num, show 1+(6689775926583349/20000000000000000000 : ℝ)+(881713673233993/6250000000000000000 : ℝ)=(100047556298404660633/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6689775926583349/20000000000000000000 : ℝ) ≤ ((6702766799648022103/6705000000000000000 : ℝ)+2*(473967531637/268200000000000 : ℝ)*(7031/50000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (6702766799648022103/6705000000000000000 : ℝ)+2*(473967531637/268200000000000 : ℝ)*(7031/50000 : ℝ)=(100016394710857/100000000000000 : ℝ) by norm_num, show 1+2*(6689775926583349/20000000000000000000 : ℝ)=(10006689775926583349/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6702766799648022103/6705000000000000000 : ℝ)*(X 1 0+X 2 0)+(473967531637/268200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (569/5000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (6702766799648022103/6705000000000000000 : ℝ)) (alpha := (473967531637/268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6702766799648022103/6705000000000000000 : ℝ)*(X 0 1+X 2 1)+(473967531637/268200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (569/5000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (6702766799648022103/6705000000000000000 : ℝ)) (alpha := (473967531637/268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6702766799648022103/6705000000000000000 : ℝ)*(X 0 2+X 1 2)+(473967531637/268200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (569/5000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (6702766799648022103/6705000000000000000 : ℝ)) (alpha := (473967531637/268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2156885301/10000000000 : ℝ)*X 0 0+(5392612499/10000000000 : ℝ)*X 0 1+(210644497/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344667447/10000000000 : ℝ)*X 1 0+(-2221042493/10000000000 : ℝ)*X 1 1+(1316528111/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66808343/125000000 : ℝ)*X 2 0+(263305623/500000000 : ℝ)*X 2 1+(-27763031/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361725133/10000000000 : ℝ)*X 0 0+(2118592261/5000000000 : ℝ)*X 0 1+(4489890151/10000000000 : ℝ)*X 0 2+(4361725133/10000000000 : ℝ)*X 1 0+(2118592261/5000000000 : ℝ)*X 1 1+(4489890151/10000000000 : ℝ)*X 1 2+(4361725133/10000000000 : ℝ)*X 2 0+(2118592261/5000000000 : ℝ)*X 2 1+(4489890151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-269611303/1250000000 : ℝ)*X 0 0+(1316607617/2500000000 : ℝ)*X 0 1+(2696146543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312568661/10000000000 : ℝ)*X 1 0+(-1047430643/5000000000 : ℝ)*X 1 1+(1078458701/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656284399/5000000000 : ℝ)*X 2 0+(2696146643/5000000000 : ℝ)*X 2 1+(-1047430699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174469383/400000000 : ℝ)*X 0 0+(1122313839/2500000000 : ℝ)*X 0 1+(4237821809/10000000000 : ℝ)*X 0 2+(174469383/400000000 : ℝ)*X 1 0+(1122313839/2500000000 : ℝ)*X 1 1+(4237821809/10000000000 : ℝ)*X 1 2+(174469383/400000000 : ℝ)*X 2 0+(1122313839/2500000000 : ℝ)*X 2 1+(4237821809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27314017485807327927851/4470000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49451657/4000000000000 : ℝ)*(base19) + (569299089/50000000000000 : ℝ)*(base23) + (46680149/100000000000000 : ℝ)*(lower2) + (156021333/100000000000000 : ℝ)*(upper3) + (21963261/20000000000000 : ℝ)*(upper5) + (5931206781612157/100000000000000 : ℝ)*(major0) + (5931206781612157/100000000000000 : ℝ)*(major1) + (5931206781612157/100000000000000 : ℝ)*(major2) + (3952584870888957/50000000000000 : ℝ)*(sp0) + (1976300928136657/25000000000000 : ℝ)*(sp1) + (63241630481919/800000000000 : ℝ)*(sp2) + (1978595092443317/50000000000000 : ℝ)*(sp3) + (35207060139/100000000000000 : ℝ)*(sp4) + (18225815671/100000000000000 : ℝ)*(sp7) + (791441682140461/20000000000000 : ℝ)*(f.failure) + (7905204948838053/100000000000000 : ℝ)*(f.sum) + (69811655150239/13410000000000000000000000000 : ℝ)*base65 + (909354489536268829/670500000000000000000000000000000 : ℝ)*base68 + (1110214297406231171/670500000000000000000000000000000 : ℝ)*base69 + (1488694861343231171/670500000000000000000000000000000 : ℝ)*base71 + (5904599229191/13410000000000000000000000000 : ℝ)*base74 + (23174731428567768829/670500000000000000000000000000000 : ℝ)*base76 + (1246677025421231171/670500000000000000000000000000000 : ℝ)*base77 + (17718709272257268829/670500000000000000000000000000000 : ℝ)*base80 + (11824475427079/13410000000000000000000000000 : ℝ)*base81 + (396251/2000000000000000000000 : ℝ)*base90 + (396251/2000000000000000000000 : ℝ)*base92 + (396251/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146134396979101017197364607/18625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1094294637/50000000000000 : ℝ)*(base19) + (604959341/20000000000000 : ℝ)*(base23) + (176021883/20000000000000 : ℝ)*(lower1) + (255847829/100000000000000 : ℝ)*(upper2) + (115306733/25000000000000 : ℝ)*(upper3) + (9451613/25000000000000 : ℝ)*(upper5) + (5961121210277207/100000000000000 : ℝ)*(major0) + (5961121210277207/100000000000000 : ℝ)*(major1) + (5961121210277207/100000000000000 : ℝ)*(major2) + (12390807799/50000000000000 : ℝ)*(sp2) + (3972537654659749/50000000000000 : ℝ)*(sp4) + (496567070045639/6250000000000 : ℝ)*(sp5) + (1589009500581439/20000000000000 : ℝ)*(sp6) + (1988583424848413/50000000000000 : ℝ)*(sp7) + (1988583424848413/50000000000000 : ℝ)*(f.failure) + (3972537654659749/50000000000000 : ℝ)*(f.sum) + (87098322313321/13410000000000000000000000000 : ℝ)*base66 + (2277216766620418679/670500000000000000000000000000000 : ℝ)*base68 + (51968443240268581321/670500000000000000000000000000000 : ℝ)*base69 + (4401162227547418679/670500000000000000000000000000000 : ℝ)*base72 + (23537929885139/13410000000000000000000000000 : ℝ)*base73 + (13272550637517418679/670500000000000000000000000000000 : ℝ)*base76 + (9909668834100418679/670500000000000000000000000000000 : ℝ)*base78 + (11680361592633418679/670500000000000000000000000000000 : ℝ)*base80 + (429843167106419/13410000000000000000000000000 : ℝ)*base81 + (68362517/5000000000000000000000 : ℝ)*base89 + (68362517/5000000000000000000000 : ℝ)*base91 + (68362517/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1163_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (569/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1163_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1163_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1163_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1163_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1163_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1163_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1612_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:45.691008+00:00
-- url     : https://prove2.me/submissions/f0d1beb8-2717-4de5-b7a8-74a6c043413c

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
theorem support_rectangle_w1612_s0_0 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-97609061/625000000 : ℝ)*x 0 + (5834419347/10000000000 : ℝ)*x 1 + (1223626409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97609061/625000000 : ℝ)^4767 ≤ (9397235593029/100000000000000 : ℝ)^3743 := by
    have hnat : (97609061 : ℕ)^4767*100000000000000^3743 ≤ 9397235593029^3743*625000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97609061 625000000 9397235593029 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5834419347/10000000000 : ℝ)^4767 ≤ (50347730244007/100000000000000 : ℝ)^3743 := by
    have hnat : (5834419347 : ℕ)^4767*100000000000000^3743 ≤ 50347730244007^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5834419347 10000000000 50347730244007 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1223626409/2500000000 : ℝ)^4767 ≤ (40255034154973/100000000000000 : ℝ)^3743 := by
    have hnat : (1223626409 : ℕ)^4767*100000000000000^3743 ≤ 40255034154973^3743*2500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223626409 2500000000 40255034154973 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97609061/625000000 : ℝ), (5834419347/10000000000 : ℝ), (1223626409/2500000000 : ℝ)] ![(9397235593029/100000000000000 : ℝ), (50347730244007/100000000000000 : ℝ), (40255034154973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97609061/625000000 : ℝ)|^4767 ≤ (9397235593029/100000000000000 : ℝ)^3743
        have hw : |(-97609061/625000000 : ℝ)|=(97609061/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5834419347/10000000000 : ℝ)|^4767 ≤ (50347730244007/100000000000000 : ℝ)^3743
        have hw : |(5834419347/10000000000 : ℝ)|=(5834419347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1223626409/2500000000 : ℝ)|^4767 ≤ (40255034154973/100000000000000 : ℝ)^3743
        have hw : |(1223626409/2500000000 : ℝ)|=(1223626409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s0_1 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5452894067/10000000000 : ℝ)*x 0 + (-416382397/2000000000 : ℝ)*x 1 + (244725271/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5452894067/10000000000 : ℝ)^4767 ≤ (23096394864639/50000000000000 : ℝ)^3743 := by
    have hnat : (5452894067 : ℕ)^4767*50000000000000^3743 ≤ 23096394864639^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452894067 10000000000 23096394864639 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416382397/2000000000 : ℝ)^4767 ≤ (3388044592753/25000000000000 : ℝ)^3743 := by
    have hnat : (416382397 : ℕ)^4767*25000000000000^3743 ≤ 3388044592753^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416382397 2000000000 3388044592753 25000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244725271/500000000 : ℝ)^4767 ≤ (40255031892463/100000000000000 : ℝ)^3743 := by
    have hnat : (244725271 : ℕ)^4767*100000000000000^3743 ≤ 40255031892463^3743*500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244725271 500000000 40255031892463 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5452894067/10000000000 : ℝ), (-416382397/2000000000 : ℝ), (244725271/500000000 : ℝ)] ![(23096394864639/50000000000000 : ℝ), (3388044592753/25000000000000 : ℝ), (40255031892463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5452894067/10000000000 : ℝ)|^4767 ≤ (23096394864639/50000000000000 : ℝ)^3743
        have hw : |(5452894067/10000000000 : ℝ)|=(5452894067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-416382397/2000000000 : ℝ)|^4767 ≤ (3388044592753/25000000000000 : ℝ)^3743
        have hw : |(-416382397/2000000000 : ℝ)|=(416382397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(244725271/500000000 : ℝ)|^4767 ≤ (40255031892463/100000000000000 : ℝ)^3743
        have hw : |(244725271/500000000 : ℝ)|=(244725271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s0_2 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (340805867/625000000 : ℝ)*x 0 + (4894505497/10000000000 : ℝ)*x 1 + (-104095607/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340805867/625000000 : ℝ)^4767 ≤ (9238557525093/20000000000000 : ℝ)^3743 := by
    have hnat : (340805867 : ℕ)^4767*20000000000000^3743 ≤ 9238557525093^3743*625000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340805867 625000000 9238557525093 20000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4894505497/10000000000 : ℝ)^4767 ≤ (20127516349503/50000000000000 : ℝ)^3743 := by
    have hnat : (4894505497 : ℕ)^4767*50000000000000^3743 ≤ 20127516349503^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4894505497 10000000000 20127516349503 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104095607/500000000 : ℝ)^4767 ≤ (6776089828007/50000000000000 : ℝ)^3743 := by
    have hnat : (104095607 : ℕ)^4767*50000000000000^3743 ≤ 6776089828007^3743*500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104095607 500000000 6776089828007 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(340805867/625000000 : ℝ), (4894505497/10000000000 : ℝ), (-104095607/500000000 : ℝ)] ![(9238557525093/20000000000000 : ℝ), (20127516349503/50000000000000 : ℝ), (6776089828007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(340805867/625000000 : ℝ)|^4767 ≤ (9238557525093/20000000000000 : ℝ)^3743
        have hw : |(340805867/625000000 : ℝ)|=(340805867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4894505497/10000000000 : ℝ)|^4767 ≤ (20127516349503/50000000000000 : ℝ)^3743
        have hw : |(4894505497/10000000000 : ℝ)|=(4894505497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104095607/500000000 : ℝ)|^4767 ≤ (6776089828007/50000000000000 : ℝ)^3743
        have hw : |(-104095607/500000000 : ℝ)|=(104095607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s0_3 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2054399741/5000000000 : ℝ)*x 0 + (1537310611/5000000000 : ℝ)*x 1 + (2695197783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054399741/5000000000 : ℝ)^4767 ≤ (3221336610739/10000000000000 : ℝ)^3743 := by
    have hnat : (2054399741 : ℕ)^4767*10000000000000^3743 ≤ 3221336610739^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054399741 5000000000 3221336610739 10000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537310611/5000000000 : ℝ)^4767 ≤ (22267066814163/100000000000000 : ℝ)^3743 := by
    have hnat : (1537310611 : ℕ)^4767*100000000000000^3743 ≤ 22267066814163^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537310611 5000000000 22267066814163 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695197783/5000000000 : ℝ)^4767 ≤ (1137989176549/2500000000000 : ℝ)^3743 := by
    have hnat : (2695197783 : ℕ)^4767*2500000000000^3743 ≤ 1137989176549^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695197783 5000000000 1137989176549 2500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2054399741/5000000000 : ℝ), (1537310611/5000000000 : ℝ), (2695197783/5000000000 : ℝ)] ![(3221336610739/10000000000000 : ℝ), (22267066814163/100000000000000 : ℝ), (1137989176549/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2054399741/5000000000 : ℝ)|^4767 ≤ (3221336610739/10000000000000 : ℝ)^3743
        have hw : |(2054399741/5000000000 : ℝ)|=(2054399741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1537310611/5000000000 : ℝ)|^4767 ≤ (22267066814163/100000000000000 : ℝ)^3743
        have hw : |(1537310611/5000000000 : ℝ)|=(1537310611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695197783/5000000000 : ℝ)|^4767 ≤ (1137989176549/2500000000000 : ℝ)^3743
        have hw : |(2695197783/5000000000 : ℝ)|=(2695197783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s0_4 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-782255457/5000000000 : ℝ)*x 0 + (983654871/2000000000 : ℝ)*x 1 + (5809807519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (782255457/5000000000 : ℝ)^4767 ≤ (4709218456921/50000000000000 : ℝ)^3743 := by
    have hnat : (782255457 : ℕ)^4767*50000000000000^3743 ≤ 4709218456921^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782255457 5000000000 4709218456921 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983654871/2000000000 : ℝ)^4767 ≤ (8100833346817/20000000000000 : ℝ)^3743 := by
    have hnat : (983654871 : ℕ)^4767*20000000000000^3743 ≤ 8100833346817^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983654871 2000000000 8100833346817 20000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5809807519/10000000000 : ℝ)^4767 ≤ (1001547926711/2000000000000 : ℝ)^3743 := by
    have hnat : (5809807519 : ℕ)^4767*2000000000000^3743 ≤ 1001547926711^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5809807519 10000000000 1001547926711 2000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-782255457/5000000000 : ℝ), (983654871/2000000000 : ℝ), (5809807519/10000000000 : ℝ)] ![(4709218456921/50000000000000 : ℝ), (8100833346817/20000000000000 : ℝ), (1001547926711/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-782255457/5000000000 : ℝ)|^4767 ≤ (4709218456921/50000000000000 : ℝ)^3743
        have hw : |(-782255457/5000000000 : ℝ)|=(782255457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(983654871/2000000000 : ℝ)|^4767 ≤ (8100833346817/20000000000000 : ℝ)^3743
        have hw : |(983654871/2000000000 : ℝ)|=(983654871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5809807519/10000000000 : ℝ)|^4767 ≤ (1001547926711/2000000000000 : ℝ)^3743
        have hw : |(5809807519/10000000000 : ℝ)|=(5809807519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s0_5 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196196003/10000000000 : ℝ)*x 0 + (-233321871/2000000000 : ℝ)*x 1 + (1452451947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196196003/10000000000 : ℝ)^4767 ≤ (43441371229859/100000000000000 : ℝ)^3743 := by
    have hnat : (5196196003 : ℕ)^4767*100000000000000^3743 ≤ 43441371229859^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196196003 10000000000 43441371229859 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233321871/2000000000 : ℝ)^4767 ≤ (202538421139/3125000000000 : ℝ)^3743 := by
    have hnat : (233321871 : ℕ)^4767*3125000000000^3743 ≤ 202538421139^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233321871 2000000000 202538421139 3125000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1452451947/2500000000 : ℝ)^4767 ≤ (5007739928851/10000000000000 : ℝ)^3743 := by
    have hnat : (1452451947 : ℕ)^4767*10000000000000^3743 ≤ 5007739928851^3743*2500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452451947 2500000000 5007739928851 10000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196196003/10000000000 : ℝ), (-233321871/2000000000 : ℝ), (1452451947/2500000000 : ℝ)] ![(43441371229859/100000000000000 : ℝ), (202538421139/3125000000000 : ℝ), (5007739928851/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196196003/10000000000 : ℝ)|^4767 ≤ (43441371229859/100000000000000 : ℝ)^3743
        have hw : |(5196196003/10000000000 : ℝ)|=(5196196003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-233321871/2000000000 : ℝ)|^4767 ≤ (202538421139/3125000000000 : ℝ)^3743
        have hw : |(-233321871/2000000000 : ℝ)|=(233321871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1452451947/2500000000 : ℝ)|^4767 ≤ (5007739928851/10000000000000 : ℝ)^3743
        have hw : |(1452451947/2500000000 : ℝ)|=(1452451947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s0_6 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196196167/10000000000 : ℝ)*x 0 + (5809807383/10000000000 : ℝ)*x 1 + (-145826217/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196196167/10000000000 : ℝ)^4767 ≤ (43441372976031/100000000000000 : ℝ)^3743 := by
    have hnat : (5196196167 : ℕ)^4767*100000000000000^3743 ≤ 43441372976031^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196196167 10000000000 43441372976031 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5809807383/10000000000 : ℝ)^4767 ≤ (50077394842603/100000000000000 : ℝ)^3743 := by
    have hnat : (5809807383 : ℕ)^4767*100000000000000^3743 ≤ 50077394842603^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5809807383 10000000000 50077394842603 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145826217/1250000000 : ℝ)^4767 ≤ (1296246434443/20000000000000 : ℝ)^3743 := by
    have hnat : (145826217 : ℕ)^4767*20000000000000^3743 ≤ 1296246434443^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145826217 1250000000 1296246434443 20000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196196167/10000000000 : ℝ), (5809807383/10000000000 : ℝ), (-145826217/1250000000 : ℝ)] ![(43441372976031/100000000000000 : ℝ), (50077394842603/100000000000000 : ℝ), (1296246434443/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196196167/10000000000 : ℝ)|^4767 ≤ (43441372976031/100000000000000 : ℝ)^3743
        have hw : |(5196196167/10000000000 : ℝ)|=(5196196167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5809807383/10000000000 : ℝ)|^4767 ≤ (50077394842603/100000000000000 : ℝ)^3743
        have hw : |(5809807383/10000000000 : ℝ)|=(5809807383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-145826217/1250000000 : ℝ)|^4767 ≤ (1296246434443/20000000000000 : ℝ)^3743
        have hw : |(-145826217/1250000000 : ℝ)|=(145826217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s0_7 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4115616273/10000000000 : ℝ)*x 0 + (5331833191/10000000000 : ℝ)*x 1 + (48988443/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4115616273/10000000000 : ℝ)^4767 ≤ (32281446958091/100000000000000 : ℝ)^3743 := by
    have hnat : (4115616273 : ℕ)^4767*100000000000000^3743 ≤ 32281446958091^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115616273 10000000000 32281446958091 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5331833191/10000000000 : ℝ)^4767 ≤ (44890678206321/100000000000000 : ℝ)^3743 := by
    have hnat : (5331833191 : ℕ)^4767*100000000000000^3743 ≤ 44890678206321^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5331833191 10000000000 44890678206321 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48988443/156250000 : ℝ)^4767 ≤ (2853484353623/12500000000000 : ℝ)^3743 := by
    have hnat : (48988443 : ℕ)^4767*12500000000000^3743 ≤ 2853484353623^3743*156250000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48988443 156250000 2853484353623 12500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4115616273/10000000000 : ℝ), (5331833191/10000000000 : ℝ), (48988443/156250000 : ℝ)] ![(32281446958091/100000000000000 : ℝ), (44890678206321/100000000000000 : ℝ), (2853484353623/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4115616273/10000000000 : ℝ)|^4767 ≤ (32281446958091/100000000000000 : ℝ)^3743
        have hw : |(4115616273/10000000000 : ℝ)|=(4115616273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5331833191/10000000000 : ℝ)|^4767 ≤ (44890678206321/100000000000000 : ℝ)^3743
        have hw : |(5331833191/10000000000 : ℝ)|=(5331833191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(48988443/156250000 : ℝ)|^4767 ≤ (2853484353623/12500000000000 : ℝ)^3743
        have hw : |(48988443/156250000 : ℝ)|=(48988443/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1612_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2033/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6049/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4763/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4763 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4763*1^1024 ≤ 0^1024*1^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4763/1024 : ℝ) ≤ (1409402057200501369/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4763 ≤ (1409402057200501369/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4763*100000000000000000000^1024 ≤ 1409402057200501369^1024*5^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1409402057200501369 100000000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1409402057200501369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4763 := by
      have hnat : (1 : ℕ)^1024*1^4763 ≤ 1^4763*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101409402057200501369/100000000000000000000 : ℝ) ≤ (10030134581512331/10000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (101409402057200501369/100000000000000000000 : ℝ)^1024 ≤ (10030134581512331/10000000000000000 : ℝ)^4763 := by
      have hnat : (101409402057200501369 : ℕ)^1024*10000000000000000^4763 ≤ 10030134581512331^4763*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101409402057200501369 100000000000000000000 10030134581512331 10000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030134581512331/10000000000000000 : ℝ)) (X := (101409402057200501369/100000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51409402057200501369/50000000000000000000 : ℝ) ≤ (5030134581512331/5000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (51409402057200501369/50000000000000000000 : ℝ)^1024 ≤ (5030134581512331/5000000000000000 : ℝ)^4763 := by
      have hnat : (51409402057200501369 : ℕ)^1024*5000000000000000^4763 ≤ 5030134581512331^4763*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51409402057200501369 50000000000000000000 5030134581512331 5000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030134581512331/5000000000000000 : ℝ)) (X := (51409402057200501369/50000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30134581512331/4000000000000000 : ℝ)*(0 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30134581512331/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1409402057200501369/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30134581512331/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4763/1024 : ℝ) := by
    rw [show (1 : ℝ)+(30134581512331/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10030134581512331/10000000000000000 : ℝ) by norm_num, show 1+(1409402057200501369/100000000000000000000 : ℝ)+(0 : ℝ)=(101409402057200501369/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1409402057200501369/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30134581512331/4000000000000000 : ℝ)*(2/5 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30134581512331/4000000000000000 : ℝ)*(2/5 : ℝ)=(5030134581512331/5000000000000000 : ℝ) by norm_num, show 1+2*(1409402057200501369/100000000000000000000 : ℝ)=(51409402057200501369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30134581512331/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30134581512331/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30134581512331/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30134581512331/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30134581512331/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30134581512331/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-97609061/625000000 : ℝ)*X 0 0+(5834419347/10000000000 : ℝ)*X 0 1+(1223626409/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5452894067/10000000000 : ℝ)*X 1 0+(-416382397/2000000000 : ℝ)*X 1 1+(244725271/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((340805867/625000000 : ℝ)*X 2 0+(4894505497/10000000000 : ℝ)*X 2 1+(-104095607/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2054399741/5000000000 : ℝ)*X 0 0+(1537310611/5000000000 : ℝ)*X 0 1+(2695197783/5000000000 : ℝ)*X 0 2+(2054399741/5000000000 : ℝ)*X 1 0+(1537310611/5000000000 : ℝ)*X 1 1+(2695197783/5000000000 : ℝ)*X 1 2+(2054399741/5000000000 : ℝ)*X 2 0+(1537310611/5000000000 : ℝ)*X 2 1+(2695197783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-782255457/5000000000 : ℝ)*X 0 0+(983654871/2000000000 : ℝ)*X 0 1+(5809807519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5196196003/10000000000 : ℝ)*X 1 0+(-233321871/2000000000 : ℝ)*X 1 1+(1452451947/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5196196167/10000000000 : ℝ)*X 2 0+(5809807383/10000000000 : ℝ)*X 2 1+(-145826217/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4115616273/10000000000 : ℝ)*X 0 0+(5331833191/10000000000 : ℝ)*X 0 1+(48988443/156250000 : ℝ)*X 0 2+(4115616273/10000000000 : ℝ)*X 1 0+(5331833191/10000000000 : ℝ)*X 1 1+(48988443/156250000 : ℝ)*X 1 2+(4115616273/10000000000 : ℝ)*X 2 0+(5331833191/10000000000 : ℝ)*X 2 1+(48988443/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214893207732892713499197/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (790428389/100000000000000 : ℝ)*(base19) + (18478989/2500000000000 : ℝ)*(base23) + (6963221/5000000000000 : ℝ)*(upper3) + (7209667/100000000000000 : ℝ)*(upper4) + (68824759/100000000000000 : ℝ)*(upper5) + (373939260424829/50000000000000 : ℝ)*(major0) + (373939260424829/50000000000000 : ℝ)*(major1) + (373939260424829/50000000000000 : ℝ)*(major2) + (531965255573151/50000000000000 : ℝ)*(sp0) + (531966178543773/50000000000000 : ℝ)*(sp1) + (531966204178187/50000000000000 : ℝ)*(sp2) + (215911122386567/50000000000000 : ℝ)*(sp3) + (82386551/3125000000000 : ℝ)*(sp4) + (1506148103/100000000000000 : ℝ)*(sp7) + (107955937730309/25000000000000 : ℝ)*(f.failure) + (531966573757967/50000000000000 : ℝ)*(f.sum) + (289851068633601/100000000000000000000000000000 : ℝ)*base66 + (703181352933601/200000000000000000000000000000 : ℝ)*base68 + (262772926066399/200000000000000000000000000000 : ℝ)*base69 + (705772895733601/200000000000000000000000000000 : ℝ)*base72 + (300585399033601/100000000000000000000000000000 : ℝ)*base74 + (2236242721933601/200000000000000000000000000000 : ℝ)*base76 + (384523004933601/200000000000000000000000000000 : ℝ)*base78 + (21759502266399/200000000000000000000000000000 : ℝ)*base79 + (50298788066399/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (13567717/2500000000000000000000 : ℝ)*base90 + (13567717/2500000000000000000000 : ℝ)*base92 + (13567717/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52148189969737429115061/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63816077/6250000000000 : ℝ)*(base19) + (26665757/2500000000000 : ℝ)*(base23) + (214634037/100000000000000 : ℝ)*(base32) + (204011923/100000000000000 : ℝ)*(upper3) + (17470411/50000000000000 : ℝ)*(upper5) + (78845822556277/10000000000000 : ℝ)*(major0) + (78845822556277/10000000000000 : ℝ)*(major1) + (78845822556277/10000000000000 : ℝ)*(major2) + (1387538133/50000000000000 : ℝ)*(sp1) + (1490490187/50000000000000 : ℝ)*(sp2) + (140207734474261/12500000000000 : ℝ)*(sp4) + (112165807966059/10000000000000 : ℝ)*(sp5) + (560828914091717/50000000000000 : ℝ)*(sp6) + (45525418687011/10000000000000 : ℝ)*(sp7) + (455254401504147/100000000000000 : ℝ)*(f.failure) + (140207734474261/12500000000000 : ℝ)*(f.sum) + (24218544991687/20000000000000000000000000000 : ℝ)*base65 + (91562353048313/40000000000000000000000000000 : ℝ)*base68 + (421170038728313/40000000000000000000000000000 : ℝ)*base70 + (178642407928313/40000000000000000000000000000 : ℝ)*base72 + (77219945951687/20000000000000000000000000000 : ℝ)*base73 + (360005597448313/40000000000000000000000000000 : ℝ)*base76 + (121123608488313/40000000000000000000000000000 : ℝ)*base78 + (453666187448313/40000000000000000000000000000 : ℝ)*base80 + (1093481768313/20000000000000000000000000000 : ℝ)*base82 + (52278989/10000000000000000000000 : ℝ)*base89 + (52278989/10000000000000000000000 : ℝ)*base91 + (52278989/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1612_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2033/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6049/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1612_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1612_s1_0 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-842114171/5000000000 : ℝ)*x 0 + (5528032671/10000000000 : ℝ)*x 1 + (5121656961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842114171/5000000000 : ℝ)^4767 ≤ (10345745802039/100000000000000 : ℝ)^3743 := by
    have hnat : (842114171 : ℕ)^4767*100000000000000^3743 ≤ 10345745802039^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842114171 5000000000 10345745802039 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528032671/10000000000 : ℝ)^4767 ≤ (23502483372161/50000000000000 : ℝ)^3743 := by
    have hnat : (5528032671 : ℕ)^4767*50000000000000^3743 ≤ 23502483372161^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528032671 10000000000 23502483372161 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5121656961/10000000000 : ℝ)^4767 ≤ (42649287435189/100000000000000 : ℝ)^3743 := by
    have hnat : (5121656961 : ℕ)^4767*100000000000000^3743 ≤ 42649287435189^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121656961 10000000000 42649287435189 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-842114171/5000000000 : ℝ), (5528032671/10000000000 : ℝ), (5121656961/10000000000 : ℝ)] ![(10345745802039/100000000000000 : ℝ), (23502483372161/50000000000000 : ℝ), (42649287435189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-842114171/5000000000 : ℝ)|^4767 ≤ (10345745802039/100000000000000 : ℝ)^3743
        have hw : |(-842114171/5000000000 : ℝ)|=(842114171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528032671/10000000000 : ℝ)|^4767 ≤ (23502483372161/50000000000000 : ℝ)^3743
        have hw : |(5528032671/10000000000 : ℝ)|=(5528032671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5121656961/10000000000 : ℝ)|^4767 ≤ (42649287435189/100000000000000 : ℝ)^3743
        have hw : |(5121656961/10000000000 : ℝ)|=(5121656961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s1_1 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268568351/500000000 : ℝ)*x 0 + (-948342803/5000000000 : ℝ)*x 1 + (5121656807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268568351/500000000 : ℝ)^4767 ≤ (2832188596061/6250000000000 : ℝ)^3743 := by
    have hnat : (268568351 : ℕ)^4767*6250000000000^3743 ≤ 2832188596061^3743*500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268568351 500000000 2832188596061 6250000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948342803/5000000000 : ℝ)^4767 ≤ (12035696648521/100000000000000 : ℝ)^3743 := by
    have hnat : (948342803 : ℕ)^4767*100000000000000^3743 ≤ 12035696648521^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948342803 5000000000 12035696648521 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5121656807/10000000000 : ℝ)^4767 ≤ (42649285801959/100000000000000 : ℝ)^3743 := by
    have hnat : (5121656807 : ℕ)^4767*100000000000000^3743 ≤ 42649285801959^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121656807 10000000000 42649285801959 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268568351/500000000 : ℝ), (-948342803/5000000000 : ℝ), (5121656807/10000000000 : ℝ)] ![(2832188596061/6250000000000 : ℝ), (12035696648521/100000000000000 : ℝ), (42649285801959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268568351/500000000 : ℝ)|^4767 ≤ (2832188596061/6250000000000 : ℝ)^3743
        have hw : |(268568351/500000000 : ℝ)|=(268568351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-948342803/5000000000 : ℝ)|^4767 ≤ (12035696648521/100000000000000 : ℝ)^3743
        have hw : |(-948342803/5000000000 : ℝ)|=(948342803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5121656807/10000000000 : ℝ)|^4767 ≤ (42649285801959/100000000000000 : ℝ)^3743
        have hw : |(5121656807/10000000000 : ℝ)|=(5121656807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s1_2 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074273367/2000000000 : ℝ)*x 0 + (2560828461/5000000000 : ℝ)*x 1 + (-948342851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074273367/2000000000 : ℝ)^4767 ≤ (2265750777463/5000000000000 : ℝ)^3743 := by
    have hnat : (1074273367 : ℕ)^4767*5000000000000^3743 ≤ 2265750777463^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074273367 2000000000 2265750777463 5000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2560828461/5000000000 : ℝ)^4767 ≤ (42649287021579/100000000000000 : ℝ)^3743 := by
    have hnat : (2560828461 : ℕ)^4767*100000000000000^3743 ≤ 42649287021579^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560828461 5000000000 42649287021579 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948342851/5000000000 : ℝ)^4767 ≤ (6017848712181/50000000000000 : ℝ)^3743 := by
    have hnat : (948342851 : ℕ)^4767*50000000000000^3743 ≤ 6017848712181^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948342851 5000000000 6017848712181 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074273367/2000000000 : ℝ), (2560828461/5000000000 : ℝ), (-948342851/5000000000 : ℝ)] ![(2265750777463/5000000000000 : ℝ), (42649287021579/100000000000000 : ℝ), (6017848712181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074273367/2000000000 : ℝ)|^4767 ≤ (2265750777463/5000000000000 : ℝ)^3743
        have hw : |(1074273367/2000000000 : ℝ)|=(1074273367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2560828461/5000000000 : ℝ)|^4767 ≤ (42649287021579/100000000000000 : ℝ)^3743
        have hw : |(2560828461/5000000000 : ℝ)|=(2560828461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948342851/5000000000 : ℝ)|^4767 ≤ (6017848712181/50000000000000 : ℝ)^3743
        have hw : |(-948342851/5000000000 : ℝ)|=(948342851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s1_3 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4199900857/10000000000 : ℝ)*x 0 + (1861060703/5000000000 : ℝ)*x 1 + (472335603/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199900857/10000000000 : ℝ)^4767 ≤ (6625150844123/20000000000000 : ℝ)^3743 := by
    have hnat : (4199900857 : ℕ)^4767*20000000000000^3743 ≤ 6625150844123^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199900857 10000000000 6625150844123 20000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1861060703/5000000000 : ℝ)^4767 ≤ (28403283515893/100000000000000 : ℝ)^3743 := by
    have hnat : (1861060703 : ℕ)^4767*100000000000000^3743 ≤ 28403283515893^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861060703 5000000000 28403283515893 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472335603/1000000000 : ℝ)^4767 ≤ (4808870281101/12500000000000 : ℝ)^3743 := by
    have hnat : (472335603 : ℕ)^4767*12500000000000^3743 ≤ 4808870281101^3743*1000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472335603 1000000000 4808870281101 12500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199900857/10000000000 : ℝ), (1861060703/5000000000 : ℝ), (472335603/1000000000 : ℝ)] ![(6625150844123/20000000000000 : ℝ), (28403283515893/100000000000000 : ℝ), (4808870281101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199900857/10000000000 : ℝ)|^4767 ≤ (6625150844123/20000000000000 : ℝ)^3743
        have hw : |(4199900857/10000000000 : ℝ)|=(4199900857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1861060703/5000000000 : ℝ)|^4767 ≤ (28403283515893/100000000000000 : ℝ)^3743
        have hw : |(1861060703/5000000000 : ℝ)|=(1861060703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(472335603/1000000000 : ℝ)|^4767 ≤ (4808870281101/12500000000000 : ℝ)^3743
        have hw : |(472335603/1000000000 : ℝ)|=(472335603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s1_4 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-84222349/500000000 : ℝ)*x 0 + (41008499/80000000 : ℝ)*x 1 + (5523559373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84222349/500000000 : ℝ)^4767 ≤ (5173728144001/50000000000000 : ℝ)^3743 := by
    have hnat : (84222349 : ℕ)^4767*50000000000000^3743 ≤ 5173728144001^3743*500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84222349 500000000 5173728144001 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41008499/80000000 : ℝ)^4767 ≤ (5337001757747/12500000000000 : ℝ)^3743 := by
    have hnat : (41008499 : ℕ)^4767*12500000000000^3743 ≤ 5337001757747^3743*80000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41008499 80000000 5337001757747 12500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5523559373/10000000000 : ℝ)^4767 ≤ (586956620433/1250000000000 : ℝ)^3743 := by
    have hnat : (5523559373 : ℕ)^4767*1250000000000^3743 ≤ 586956620433^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523559373 10000000000 586956620433 1250000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84222349/500000000 : ℝ), (41008499/80000000 : ℝ), (5523559373/10000000000 : ℝ)] ![(5173728144001/50000000000000 : ℝ), (5337001757747/12500000000000 : ℝ), (586956620433/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84222349/500000000 : ℝ)|^4767 ≤ (5173728144001/50000000000000 : ℝ)^3743
        have hw : |(-84222349/500000000 : ℝ)|=(84222349/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41008499/80000000 : ℝ)|^4767 ≤ (5337001757747/12500000000000 : ℝ)^3743
        have hw : |(41008499/80000000 : ℝ)|=(41008499/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5523559373/10000000000 : ℝ)|^4767 ≤ (586956620433/1250000000000 : ℝ)^3743
        have hw : |(5523559373/10000000000 : ℝ)|=(5523559373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s1_5 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263227867/10000000000 : ℝ)*x 0 + (-1494782657/10000000000 : ℝ)*x 1 + (2761779853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263227867/10000000000 : ℝ)^4767 ≤ (13798856689/31250000000 : ℝ)^3743 := by
    have hnat : (5263227867 : ℕ)^4767*31250000000^3743 ≤ 13798856689^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263227867 10000000000 13798856689 31250000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1494782657/10000000000 : ℝ)^4767 ≤ (555445333869/6250000000000 : ℝ)^3743 := by
    have hnat : (1494782657 : ℕ)^4767*6250000000000^3743 ≤ 555445333869^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494782657 10000000000 555445333869 6250000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2761779853/5000000000 : ℝ)^4767 ≤ (23478266619991/50000000000000 : ℝ)^3743 := by
    have hnat : (2761779853 : ℕ)^4767*50000000000000^3743 ≤ 23478266619991^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761779853 5000000000 23478266619991 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263227867/10000000000 : ℝ), (-1494782657/10000000000 : ℝ), (2761779853/5000000000 : ℝ)] ![(13798856689/31250000000 : ℝ), (555445333869/6250000000000 : ℝ), (23478266619991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263227867/10000000000 : ℝ)|^4767 ≤ (13798856689/31250000000 : ℝ)^3743
        have hw : |(5263227867/10000000000 : ℝ)|=(5263227867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1494782657/10000000000 : ℝ)|^4767 ≤ (555445333869/6250000000000 : ℝ)^3743
        have hw : |(-1494782657/10000000000 : ℝ)|=(1494782657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2761779853/5000000000 : ℝ)|^4767 ≤ (23478266619991/50000000000000 : ℝ)^3743
        have hw : |(2761779853/5000000000 : ℝ)|=(2761779853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s1_6 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263227223/10000000000 : ℝ)*x 0 + (110471199/200000000 : ℝ)*x 1 + (-93423951/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263227223/10000000000 : ℝ)^4767 ≤ (2759770907737/6250000000000 : ℝ)^3743 := by
    have hnat : (5263227223 : ℕ)^4767*6250000000000^3743 ≤ 2759770907737^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263227223 10000000000 2759770907737 6250000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110471199/200000000 : ℝ)^4767 ≤ (9391307176347/20000000000000 : ℝ)^3743 := by
    have hnat : (110471199 : ℕ)^4767*20000000000000^3743 ≤ 9391307176347^3743*200000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110471199 200000000 9391307176347 20000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93423951/625000000 : ℝ)^4767 ≤ (8887129574633/100000000000000 : ℝ)^3743 := by
    have hnat : (93423951 : ℕ)^4767*100000000000000^3743 ≤ 8887129574633^3743*625000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93423951 625000000 8887129574633 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263227223/10000000000 : ℝ), (110471199/200000000 : ℝ), (-93423951/625000000 : ℝ)] ![(2759770907737/6250000000000 : ℝ), (9391307176347/20000000000000 : ℝ), (8887129574633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263227223/10000000000 : ℝ)|^4767 ≤ (2759770907737/6250000000000 : ℝ)^3743
        have hw : |(5263227223/10000000000 : ℝ)|=(5263227223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110471199/200000000 : ℝ)|^4767 ≤ (9391307176347/20000000000000 : ℝ)^3743
        have hw : |(110471199/200000000 : ℝ)|=(110471199/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93423951/625000000 : ℝ)|^4767 ≤ (8887129574633/100000000000000 : ℝ)^3743
        have hw : |(-93423951/625000000 : ℝ)|=(93423951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s1_7 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4200438127/10000000000 : ℝ)*x 0 + (73632861/156250000 : ℝ)*x 1 + (3733141779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200438127/10000000000 : ℝ)^4767 ≤ (662623024371/2000000000000 : ℝ)^3743 := by
    have hnat : (4200438127 : ℕ)^4767*2000000000000^3743 ≤ 662623024371^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200438127 10000000000 662623024371 2000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73632861/156250000 : ℝ)^4767 ≤ (1198700605989/3125000000000 : ℝ)^3743 := by
    have hnat : (73632861 : ℕ)^4767*3125000000000^3743 ≤ 1198700605989^3743*156250000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73632861 156250000 1198700605989 3125000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3733141779/10000000000 : ℝ)^4767 ≤ (5702085873513/20000000000000 : ℝ)^3743 := by
    have hnat : (3733141779 : ℕ)^4767*20000000000000^3743 ≤ 5702085873513^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733141779 10000000000 5702085873513 20000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200438127/10000000000 : ℝ), (73632861/156250000 : ℝ), (3733141779/10000000000 : ℝ)] ![(662623024371/2000000000000 : ℝ), (1198700605989/3125000000000 : ℝ), (5702085873513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200438127/10000000000 : ℝ)|^4767 ≤ (662623024371/2000000000000 : ℝ)^3743
        have hw : |(4200438127/10000000000 : ℝ)|=(4200438127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(73632861/156250000 : ℝ)|^4767 ≤ (1198700605989/3125000000000 : ℝ)^3743
        have hw : |(73632861/156250000 : ℝ)|=(73632861/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3733141779/10000000000 : ℝ)|^4767 ≤ (5702085873513/20000000000000 : ℝ)^3743
        have hw : |(3733141779/10000000000 : ℝ)|=(3733141779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1612_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6049/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2033/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4583/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17779/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6049/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2033/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6049/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2033/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6049/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2033/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6049/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2033/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6049/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2033/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6049/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2033/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2033/50000 : ℝ) ^ (4763/1024 : ℝ) ≤ (424264578637/1250000000000000000 : ℝ) := by
    have hpowers : (2033/50000 : ℝ)^4763 ≤ (424264578637/1250000000000000000 : ℝ)^1024 := by
      have hnat : (2033 : ℕ)^4763*1250000000000000000^1024 ≤ 424264578637^1024*50000^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2033 50000 424264578637 1250000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2033/50000 : ℝ)) (X := (424264578637/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6049/25000 : ℝ) ^ (4763/1024 : ℝ) ≤ (27201639785219669/20000000000000000000 : ℝ) := by
    have hpowers : (6049/25000 : ℝ)^4763 ≤ (27201639785219669/20000000000000000000 : ℝ)^1024 := by
      have hnat : (6049 : ℕ)^4763*20000000000000000000^1024 ≤ 27201639785219669^1024*25000^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6049 25000 27201639785219669 20000000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6049/25000 : ℝ)) (X := (27201639785219669/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (625000424264578637/625000000000000000 : ℝ) ≤ (2500000364851407/2500000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (625000424264578637/625000000000000000 : ℝ)^1024 ≤ (2500000364851407/2500000000000000 : ℝ)^4763 := by
      have hnat : (625000424264578637 : ℕ)^1024*2500000000000000^4763 ≤ 2500000364851407^4763*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625000424264578637 625000000000000000 2500000364851407 2500000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000364851407/2500000000000000 : ℝ)) (X := (625000424264578637/625000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20027208428018477861/20000000000000000000 : ℝ) ≤ (5001461608497961/5000000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (20027208428018477861/20000000000000000000 : ℝ)^1024 ≤ (5001461608497961/5000000000000000 : ℝ)^4763 := by
      have hnat : (20027208428018477861 : ℕ)^1024*5000000000000000^4763 ≤ 5001461608497961^4763*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20027208428018477861 20000000000000000000 5001461608497961 5000000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001461608497961/5000000000000000 : ℝ)) (X := (20027208428018477861/20000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10027201639785219669/10000000000000000000 : ℝ) ≤ (1250730621823277/1250000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (10027201639785219669/10000000000000000000 : ℝ)^1024 ≤ (1250730621823277/1250000000000000 : ℝ)^4763 := by
      have hnat : (10027201639785219669 : ℕ)^1024*1250000000000000^4763 ≤ 1250730621823277^4763*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10027201639785219669 10000000000000000000 1250730621823277 1250000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250730621823277/1250000000000000 : ℝ)) (X := (10027201639785219669/10000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(424264578637/1250000000000000000 : ℝ) ≤ ((6289883426409719401/6290625000000000000 : ℝ)+2*(1460878795147/1006500000000000 : ℝ)*(2033/50000 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (6289883426409719401/6290625000000000000 : ℝ)+2*(1460878795147/1006500000000000 : ℝ)*(2033/50000 : ℝ)=(2500000364851407/2500000000000000 : ℝ) by norm_num, show 1+2*(424264578637/1250000000000000000 : ℝ)=(625000424264578637/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27201639785219669/20000000000000000000 : ℝ)+(424264578637/1250000000000000000 : ℝ) ≤ ((6289883426409719401/6290625000000000000 : ℝ)+(1460878795147/1006500000000000 : ℝ)*((6049/25000 : ℝ)+(2033/50000 : ℝ)))^(4763/1024 : ℝ) := by
    rw [show (6289883426409719401/6290625000000000000 : ℝ)+(1460878795147/1006500000000000 : ℝ)*((6049/25000 : ℝ)+(2033/50000 : ℝ))=(5001461608497961/5000000000000000 : ℝ) by norm_num, show 1+(27201639785219669/20000000000000000000 : ℝ)+(424264578637/1250000000000000000 : ℝ)=(20027208428018477861/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27201639785219669/20000000000000000000 : ℝ) ≤ ((6289883426409719401/6290625000000000000 : ℝ)+2*(1460878795147/1006500000000000 : ℝ)*(6049/25000 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (6289883426409719401/6290625000000000000 : ℝ)+2*(1460878795147/1006500000000000 : ℝ)*(6049/25000 : ℝ)=(1250730621823277/1250000000000000 : ℝ) by norm_num, show 1+2*(27201639785219669/20000000000000000000 : ℝ)=(10027201639785219669/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6289883426409719401/6290625000000000000 : ℝ)*(X 1 0+X 2 0)+(1460878795147/1006500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (2033/50000 : ℝ)) (hi := (6049/25000 : ℝ)) (c := (6289883426409719401/6290625000000000000 : ℝ)) (alpha := (1460878795147/1006500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6289883426409719401/6290625000000000000 : ℝ)*(X 0 1+X 2 1)+(1460878795147/1006500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (2033/50000 : ℝ)) (hi := (6049/25000 : ℝ)) (c := (6289883426409719401/6290625000000000000 : ℝ)) (alpha := (1460878795147/1006500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6289883426409719401/6290625000000000000 : ℝ)*(X 0 2+X 1 2)+(1460878795147/1006500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (2033/50000 : ℝ)) (hi := (6049/25000 : ℝ)) (c := (6289883426409719401/6290625000000000000 : ℝ)) (alpha := (1460878795147/1006500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-842114171/5000000000 : ℝ)*X 0 0+(5528032671/10000000000 : ℝ)*X 0 1+(5121656961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((268568351/500000000 : ℝ)*X 1 0+(-948342803/5000000000 : ℝ)*X 1 1+(5121656807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074273367/2000000000 : ℝ)*X 2 0+(2560828461/5000000000 : ℝ)*X 2 1+(-948342851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4199900857/10000000000 : ℝ)*X 0 0+(1861060703/5000000000 : ℝ)*X 0 1+(472335603/1000000000 : ℝ)*X 0 2+(4199900857/10000000000 : ℝ)*X 1 0+(1861060703/5000000000 : ℝ)*X 1 1+(472335603/1000000000 : ℝ)*X 1 2+(4199900857/10000000000 : ℝ)*X 2 0+(1861060703/5000000000 : ℝ)*X 2 1+(472335603/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-84222349/500000000 : ℝ)*X 0 0+(41008499/80000000 : ℝ)*X 0 1+(5523559373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5263227867/10000000000 : ℝ)*X 1 0+(-1494782657/10000000000 : ℝ)*X 1 1+(2761779853/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5263227223/10000000000 : ℝ)*X 2 0+(110471199/200000000 : ℝ)*X 2 1+(-93423951/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4200438127/10000000000 : ℝ)*X 0 0+(73632861/156250000 : ℝ)*X 0 1+(3733141779/10000000000 : ℝ)*X 0 2+(4200438127/10000000000 : ℝ)*X 1 0+(73632861/156250000 : ℝ)*X 1 1+(3733141779/10000000000 : ℝ)*X 1 2+(4200438127/10000000000 : ℝ)*X 2 0+(73632861/156250000 : ℝ)*X 2 1+(3733141779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8351674536957061536078917/953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92405031/50000000000000 : ℝ)*(base1) + (1773539439/100000000000000 : ℝ)*(base19) + (844392407/50000000000000 : ℝ)*(base23) + (117015617/50000000000000 : ℝ)*(upper3) + (8222459/5000000000000 : ℝ)*(upper5) + (43244763385511/2500000000000 : ℝ)*(major0) + (43244763385511/2500000000000 : ℝ)*(major1) + (43244763385511/2500000000000 : ℝ)*(major2) + (1230395262576033/50000000000000 : ℝ)*(sp0) + (2460800973108673/100000000000000 : ℝ)*(sp1) + (1230400528931649/50000000000000 : ℝ)*(sp2) + (31211630047553/3125000000000 : ℝ)*(sp3) + (3101576527/25000000000000 : ℝ)*(sp4) + (284289029/5000000000000 : ℝ)*(sp7) + (499389016056169/50000000000000 : ℝ)*(f.failure) + (153800171665507/6250000000000 : ℝ)*(f.sum) + (3239256663017/1258125000000000000000000000 : ℝ)*base65 + (29243806684569259/3931640625000000000000000000000 : ℝ)*base67 + (997667228010029/982910156250000000000000000000 : ℝ)*base70 + (68432802559917661/15726562500000000000000000000000 : ℝ)*base71 + (15344317138583/5032500000000000000000000000 : ℝ)*base73 + (48022031950350947/31453125000000000000000000000000 : ℝ)*base75 + (9981090120819259/3931640625000000000000000000000 : ℝ)*base77 + (90415988288198911/15726562500000000000000000000000 : ℝ)*base79 + (2275967237897/1258125000000000000000000000 : ℝ)*base81 + (60301897/5000000000000000000000 : ℝ)*base90 + (60301897/5000000000000000000000 : ℝ)*base92 + (60301897/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27471772809432239979824583/4193750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (682983811/50000000000000 : ℝ)*(base19) + (282865373/25000000000000 : ℝ)*(base23) + (23341281/50000000000000 : ℝ)*(upper2) + (70401751/25000000000000 : ℝ)*(upper3) + (1136471/2000000000000 : ℝ)*(upper5) + (70736231756461/4000000000000 : ℝ)*(major0) + (70736231756461/4000000000000 : ℝ)*(major1) + (70736231756461/4000000000000 : ℝ)*(major2) + (1286487009/12500000000000 : ℝ)*(sp1) + (4771637117/50000000000000 : ℝ)*(sp2) + (628934238647097/25000000000000 : ℝ)*(sp4) + (1257862648362347/50000000000000 : ℝ)*(sp5) + (1257863139926331/50000000000000 : ℝ)*(sp6) + (510537207439891/50000000000000 : ℝ)*(sp7) + (510537207439891/50000000000000 : ℝ)*(f.failure) + (628934238647097/25000000000000 : ℝ)*(f.sum) + (1321886601161/402600000000000000000000000 : ℝ)*base65 + (147506279513456389/25162500000000000000000000000000 : ℝ)*base68 + (43183260925481389/25162500000000000000000000000000 : ℝ)*base70 + (102805013314856389/25162500000000000000000000000000 : ℝ)*base72 + (3324032486173/2013000000000000000000000000 : ℝ)*base73 + (87332913993881389/25162500000000000000000000000000 : ℝ)*base76 + (32069549020031389/25162500000000000000000000000000 : ℝ)*base78 + (34167664850006389/25162500000000000000000000000000 : ℝ)*base80 + (5967872102833/2013000000000000000000000000 : ℝ)*base81 + (16504883/5000000000000000000000 : ℝ)*base90 + (16504883/5000000000000000000000 : ℝ)*base92 + (16504883/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1612_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6049/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2033/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17779/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1612_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1612_s2_0 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-848929843/5000000000 : ℝ)*x 0 + (546586971/1000000000 : ℝ)*x 1 + (2587446097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848929843/5000000000 : ℝ)^4767 ≤ (5226252393911/50000000000000 : ℝ)^3743 := by
    have hnat : (848929843 : ℕ)^4767*50000000000000^3743 ≤ 5226252393911^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848929843 5000000000 5226252393911 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546586971/1000000000 : ℝ)^4767 ≤ (23166413333079/50000000000000 : ℝ)^3743 := by
    have hnat : (546586971 : ℕ)^4767*50000000000000^3743 ≤ 23166413333079^3743*1000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546586971 1000000000 23166413333079 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587446097/5000000000 : ℝ)^4767 ≤ (21607334259173/50000000000000 : ℝ)^3743 := by
    have hnat : (2587446097 : ℕ)^4767*50000000000000^3743 ≤ 21607334259173^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587446097 5000000000 21607334259173 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-848929843/5000000000 : ℝ), (546586971/1000000000 : ℝ), (2587446097/5000000000 : ℝ)] ![(5226252393911/50000000000000 : ℝ), (23166413333079/50000000000000 : ℝ), (21607334259173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-848929843/5000000000 : ℝ)|^4767 ≤ (5226252393911/50000000000000 : ℝ)^3743
        have hw : |(-848929843/5000000000 : ℝ)|=(848929843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546586971/1000000000 : ℝ)|^4767 ≤ (23166413333079/50000000000000 : ℝ)^3743
        have hw : |(546586971/1000000000 : ℝ)|=(546586971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587446097/5000000000 : ℝ)|^4767 ≤ (21607334259173/50000000000000 : ℝ)^3743
        have hw : |(2587446097/5000000000 : ℝ)|=(2587446097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s2_1 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355153769/10000000000 : ℝ)*x 0 + (-1848102081/10000000000 : ℝ)*x 1 + (5174892089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355153769/10000000000 : ℝ)^4767 ≤ (45140887669109/100000000000000 : ℝ)^3743 := by
    have hnat : (5355153769 : ℕ)^4767*100000000000000^3743 ≤ 45140887669109^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355153769 10000000000 45140887669109 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1848102081/10000000000 : ℝ)^4767 ≤ (582222245289/5000000000000 : ℝ)^3743 := by
    have hnat : (1848102081 : ℕ)^4767*5000000000000^3743 ≤ 582222245289^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848102081 10000000000 582222245289 5000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174892089/10000000000 : ℝ)^4767 ≤ (345717339213/800000000000 : ℝ)^3743 := by
    have hnat : (5174892089 : ℕ)^4767*800000000000^3743 ≤ 345717339213^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174892089 10000000000 345717339213 800000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355153769/10000000000 : ℝ), (-1848102081/10000000000 : ℝ), (5174892089/10000000000 : ℝ)] ![(45140887669109/100000000000000 : ℝ), (582222245289/5000000000000 : ℝ), (345717339213/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355153769/10000000000 : ℝ)|^4767 ≤ (45140887669109/100000000000000 : ℝ)^3743
        have hw : |(5355153769/10000000000 : ℝ)|=(5355153769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1848102081/10000000000 : ℝ)|^4767 ≤ (582222245289/5000000000000 : ℝ)^3743
        have hw : |(-1848102081/10000000000 : ℝ)|=(1848102081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174892089/10000000000 : ℝ)|^4767 ≤ (345717339213/800000000000 : ℝ)^3743
        have hw : |(5174892089/10000000000 : ℝ)|=(5174892089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s2_2 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338788427/2500000000 : ℝ)*x 0 + (5174892109/10000000000 : ℝ)*x 1 + (-924051069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338788427/2500000000 : ℝ)^4767 ≤ (22570443507121/50000000000000 : ℝ)^3743 := by
    have hnat : (1338788427 : ℕ)^4767*50000000000000^3743 ≤ 22570443507121^3743*2500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338788427 2500000000 22570443507121 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174892109/10000000000 : ℝ)^4767 ≤ (21607333807167/50000000000000 : ℝ)^3743 := by
    have hnat : (5174892109 : ℕ)^4767*50000000000000^3743 ≤ 21607333807167^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174892109 10000000000 21607333807167 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924051069/5000000000 : ℝ)^4767 ≤ (1455555670397/12500000000000 : ℝ)^3743 := by
    have hnat : (924051069 : ℕ)^4767*12500000000000^3743 ≤ 1455555670397^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924051069 5000000000 1455555670397 12500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338788427/2500000000 : ℝ), (5174892109/10000000000 : ℝ), (-924051069/5000000000 : ℝ)] ![(22570443507121/50000000000000 : ℝ), (21607333807167/50000000000000 : ℝ), (1455555670397/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338788427/2500000000 : ℝ)|^4767 ≤ (22570443507121/50000000000000 : ℝ)^3743
        have hw : |(1338788427/2500000000 : ℝ)|=(1338788427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174892109/10000000000 : ℝ)|^4767 ≤ (21607333807167/50000000000000 : ℝ)^3743
        have hw : |(5174892109/10000000000 : ℝ)|=(5174892109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-924051069/5000000000 : ℝ)|^4767 ≤ (1455555670397/12500000000000 : ℝ)^3743
        have hw : |(-924051069/5000000000 : ℝ)|=(924051069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s2_3 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2104982269/5000000000 : ℝ)*x 0 + (965804889/2500000000 : ℝ)*x 1 + (916026811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104982269/5000000000 : ℝ)^4767 ≤ (33226877504853/100000000000000 : ℝ)^3743 := by
    have hnat : (2104982269 : ℕ)^4767*100000000000000^3743 ≤ 33226877504853^3743*5000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104982269 5000000000 33226877504853 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965804889/2500000000 : ℝ)^4767 ≤ (2978160519923/10000000000000 : ℝ)^3743 := by
    have hnat : (965804889 : ℕ)^4767*10000000000000^3743 ≤ 2978160519923^3743*2500000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965804889 2500000000 2978160519923 10000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (916026811/2000000000 : ℝ)^4767 ≤ (18495758639769/50000000000000 : ℝ)^3743 := by
    have hnat : (916026811 : ℕ)^4767*50000000000000^3743 ≤ 18495758639769^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916026811 2000000000 18495758639769 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2104982269/5000000000 : ℝ), (965804889/2500000000 : ℝ), (916026811/2000000000 : ℝ)] ![(33226877504853/100000000000000 : ℝ), (2978160519923/10000000000000 : ℝ), (18495758639769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2104982269/5000000000 : ℝ)|^4767 ≤ (33226877504853/100000000000000 : ℝ)^3743
        have hw : |(2104982269/5000000000 : ℝ)|=(2104982269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965804889/2500000000 : ℝ)|^4767 ≤ (2978160519923/10000000000000 : ℝ)^3743
        have hw : |(965804889/2500000000 : ℝ)|=(965804889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(916026811/2000000000 : ℝ)|^4767 ≤ (18495758639769/50000000000000 : ℝ)^3743
        have hw : |(916026811/2000000000 : ℝ)|=(916026811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s2_4 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1697940239/10000000000 : ℝ)*x 0 + (1035431591/2000000000 : ℝ)*x 1 + (136589471/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1697940239/10000000000 : ℝ)^4767 ≤ (10453136367927/100000000000000 : ℝ)^3743 := by
    have hnat : (1697940239 : ℕ)^4767*100000000000000^3743 ≤ 10453136367927^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697940239 10000000000 10453136367927 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035431591/2000000000 : ℝ)^4767 ≤ (43238767312279/100000000000000 : ℝ)^3743 := by
    have hnat : (1035431591 : ℕ)^4767*100000000000000^3743 ≤ 43238767312279^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035431591 2000000000 43238767312279 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136589471/250000000 : ℝ)^4767 ≤ (46308096308967/100000000000000 : ℝ)^3743 := by
    have hnat : (136589471 : ℕ)^4767*100000000000000^3743 ≤ 46308096308967^3743*250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136589471 250000000 46308096308967 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1697940239/10000000000 : ℝ), (1035431591/2000000000 : ℝ), (136589471/250000000 : ℝ)] ![(10453136367927/100000000000000 : ℝ), (43238767312279/100000000000000 : ℝ), (46308096308967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1697940239/10000000000 : ℝ)|^4767 ≤ (10453136367927/100000000000000 : ℝ)^3743
        have hw : |(-1697940239/10000000000 : ℝ)|=(1697940239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035431591/2000000000 : ℝ)|^4767 ≤ (43238767312279/100000000000000 : ℝ)^3743
        have hw : |(1035431591/2000000000 : ℝ)|=(1035431591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136589471/250000000 : ℝ)|^4767 ≤ (46308096308967/100000000000000 : ℝ)^3743
        have hw : |(136589471/250000000 : ℝ)|=(136589471/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s2_5 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41233117/78125000 : ℝ)*x 0 + (-1559415571/10000000000 : ℝ)*x 1 + (5463578653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41233117/78125000 : ℝ)^4767 ≤ (44312517366947/100000000000000 : ℝ)^3743 := by
    have hnat : (41233117 : ℕ)^4767*100000000000000^3743 ≤ 44312517366947^3743*78125000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41233117 78125000 44312517366947 100000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559415571/10000000000 : ℝ)^4767 ≤ (4689694163911/50000000000000 : ℝ)^3743 := by
    have hnat : (1559415571 : ℕ)^4767*50000000000000^3743 ≤ 4689694163911^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559415571 10000000000 4689694163911 50000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463578653/10000000000 : ℝ)^4767 ≤ (2894255893149/6250000000000 : ℝ)^3743 := by
    have hnat : (5463578653 : ℕ)^4767*6250000000000^3743 ≤ 2894255893149^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463578653 10000000000 2894255893149 6250000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41233117/78125000 : ℝ), (-1559415571/10000000000 : ℝ), (5463578653/10000000000 : ℝ)] ![(44312517366947/100000000000000 : ℝ), (4689694163911/50000000000000 : ℝ), (2894255893149/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41233117/78125000 : ℝ)|^4767 ≤ (44312517366947/100000000000000 : ℝ)^3743
        have hw : |(41233117/78125000 : ℝ)|=(41233117/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1559415571/10000000000 : ℝ)|^4767 ≤ (4689694163911/50000000000000 : ℝ)^3743
        have hw : |(-1559415571/10000000000 : ℝ)|=(1559415571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463578653/10000000000 : ℝ)|^4767 ≤ (2894255893149/6250000000000 : ℝ)^3743
        have hw : |(5463578653/10000000000 : ℝ)|=(5463578653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s2_6 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105556769/200000000 : ℝ)*x 0 + (5463579761/10000000000 : ℝ)*x 1 + (-194926843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105556769/200000000 : ℝ)^4767 ≤ (553906396781/1250000000000 : ℝ)^3743 := by
    have hnat : (105556769 : ℕ)^4767*1250000000000^3743 ≤ 553906396781^3743*200000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105556769 200000000 553906396781 1250000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463579761/10000000000 : ℝ)^4767 ≤ (1157702656269/2500000000000 : ℝ)^3743 := by
    have hnat : (5463579761 : ℕ)^4767*2500000000000^3743 ≤ 1157702656269^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463579761 10000000000 1157702656269 2500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194926843/1250000000 : ℝ)^4767 ≤ (2344845498217/25000000000000 : ℝ)^3743 := by
    have hnat : (194926843 : ℕ)^4767*25000000000000^3743 ≤ 2344845498217^3743*1250000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194926843 1250000000 2344845498217 25000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105556769/200000000 : ℝ), (5463579761/10000000000 : ℝ), (-194926843/1250000000 : ℝ)] ![(553906396781/1250000000000 : ℝ), (1157702656269/2500000000000 : ℝ), (2344845498217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105556769/200000000 : ℝ)|^4767 ≤ (553906396781/1250000000000 : ℝ)^3743
        have hw : |(105556769/200000000 : ℝ)|=(105556769/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463579761/10000000000 : ℝ)|^4767 ≤ (1157702656269/2500000000000 : ℝ)^3743
        have hw : |(5463579761/10000000000 : ℝ)|=(5463579761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194926843/1250000000 : ℝ)|^4767 ≤ (2344845498217/25000000000000 : ℝ)^3743
        have hw : |(-194926843/1250000000 : ℝ)|=(194926843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1612_s2_7 (p : ℝ) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4210162713/10000000000 : ℝ)*x 0 + (182982049/400000000 : ℝ)*x 1 + (773772707/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4210162713/10000000000 : ℝ)^4767 ≤ (6645773899821/20000000000000 : ℝ)^3743 := by
    have hnat : (4210162713 : ℕ)^4767*20000000000000^3743 ≤ 6645773899821^3743*10000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4210162713 10000000000 6645773899821 20000000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182982049/400000000 : ℝ)^4767 ≤ (577095335981/1562500000000 : ℝ)^3743 := by
    have hnat : (182982049 : ℕ)^4767*1562500000000^3743 ≤ 577095335981^3743*400000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182982049 400000000 577095335981 1562500000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773772707/2000000000 : ℝ)^4767 ≤ (745925724589/2500000000000 : ℝ)^3743 := by
    have hnat : (773772707 : ℕ)^4767*2500000000000^3743 ≤ 745925724589^3743*2000000000^4767 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773772707 2000000000 745925724589 2500000000000 4767 3743 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4767/1024 : ℝ)) 4767 3743 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4210162713/10000000000 : ℝ), (182982049/400000000 : ℝ), (773772707/2000000000 : ℝ)] ![(6645773899821/20000000000000 : ℝ), (577095335981/1562500000000 : ℝ), (745925724589/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4210162713/10000000000 : ℝ)|^4767 ≤ (6645773899821/20000000000000 : ℝ)^3743
        have hw : |(4210162713/10000000000 : ℝ)|=(4210162713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(182982049/400000000 : ℝ)|^4767 ≤ (577095335981/1562500000000 : ℝ)^3743
        have hw : |(182982049/400000000 : ℝ)|=(182982049/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(773772707/2000000000 : ℝ)|^4767 ≤ (745925724589/2500000000000 : ℝ)^3743
        have hw : |(773772707/2000000000 : ℝ)|=(773772707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1612_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2579/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3297/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4583/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4583/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4583/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4583/50000 : ℝ) ^ (4763/1024 : ℝ) ≤ (1488392322972071/100000000000000000000 : ℝ) := by
    have hpowers : (4583/50000 : ℝ)^4763 ≤ (1488392322972071/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4583 : ℕ)^4763*100000000000000000000^1024 ≤ 1488392322972071^1024*50000^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4583 50000 1488392322972071 100000000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4583/50000 : ℝ)) (X := (1488392322972071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17779/100000 : ℝ) ^ (4763/1024 : ℝ) ≤ (32437215557963089/100000000000000000000 : ℝ) := by
    have hpowers : (17779/100000 : ℝ)^4763 ≤ (32437215557963089/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17779 : ℕ)^4763*100000000000000000000^1024 ≤ 32437215557963089^1024*100000^4763 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17779 100000 32437215557963089 100000000000000000000 4763 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17779/100000 : ℝ)) (X := (32437215557963089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001488392322972071/50000000000000000000 : ℝ) ≤ (2500015999327433/2500000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (50001488392322972071/50000000000000000000 : ℝ)^1024 ≤ (2500015999327433/2500000000000000 : ℝ)^4763 := by
      have hnat : (50001488392322972071 : ℕ)^1024*2500000000000000^4763 ≤ 2500015999327433^4763*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001488392322972071 50000000000000000000 2500015999327433 2500000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500015999327433/2500000000000000 : ℝ)) (X := (50001488392322972071/50000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500848140197023379/2500000000000000000 : ℝ) ≤ (2500182317853571/2500000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (2500848140197023379/2500000000000000000 : ℝ)^1024 ≤ (2500182317853571/2500000000000000 : ℝ)^4763 := by
      have hnat : (2500848140197023379 : ℕ)^1024*2500000000000000^4763 ≤ 2500182317853571^4763*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500848140197023379 2500000000000000000 2500182317853571 2500000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500182317853571/2500000000000000 : ℝ)) (X := (2500848140197023379/2500000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032437215557963089/50000000000000000000 : ℝ) ≤ (2500348636379709/2500000000000000 : ℝ) ^ (4763/1024 : ℝ) := by
    have hpowers : (50032437215557963089/50000000000000000000 : ℝ)^1024 ≤ (2500348636379709/2500000000000000 : ℝ)^4763 := by
      have hnat : (50032437215557963089 : ℕ)^1024*2500000000000000^4763 ≤ 2500348636379709^4763*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032437215557963089 50000000000000000000 2500348636379709 2500000000000000 1024 4763 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500348636379709/2500000000000000 : ℝ)) (X := (50032437215557963089/50000000000000000000 : ℝ)) (by norm_num) 4763 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1488392322972071/100000000000000000000 : ℝ) ≤ ((21529588850986018613/21532500000000000000 : ℝ)+2*(83159263069/107662500000000 : ℝ)*(4583/50000 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (21529588850986018613/21532500000000000000 : ℝ)+2*(83159263069/107662500000000 : ℝ)*(4583/50000 : ℝ)=(2500015999327433/2500000000000000 : ℝ) by norm_num, show 1+2*(1488392322972071/100000000000000000000 : ℝ)=(50001488392322972071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32437215557963089/100000000000000000000 : ℝ)+(1488392322972071/100000000000000000000 : ℝ) ≤ ((21529588850986018613/21532500000000000000 : ℝ)+(83159263069/107662500000000 : ℝ)*((17779/100000 : ℝ)+(4583/50000 : ℝ)))^(4763/1024 : ℝ) := by
    rw [show (21529588850986018613/21532500000000000000 : ℝ)+(83159263069/107662500000000 : ℝ)*((17779/100000 : ℝ)+(4583/50000 : ℝ))=(2500182317853571/2500000000000000 : ℝ) by norm_num, show 1+(32437215557963089/100000000000000000000 : ℝ)+(1488392322972071/100000000000000000000 : ℝ)=(2500848140197023379/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32437215557963089/100000000000000000000 : ℝ) ≤ ((21529588850986018613/21532500000000000000 : ℝ)+2*(83159263069/107662500000000 : ℝ)*(17779/100000 : ℝ))^(4763/1024 : ℝ) := by
    rw [show (21529588850986018613/21532500000000000000 : ℝ)+2*(83159263069/107662500000000 : ℝ)*(17779/100000 : ℝ)=(2500348636379709/2500000000000000 : ℝ) by norm_num, show 1+2*(32437215557963089/100000000000000000000 : ℝ)=(50032437215557963089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21529588850986018613/21532500000000000000 : ℝ)*(X 1 0+X 2 0)+(83159263069/107662500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (4583/50000 : ℝ)) (hi := (17779/100000 : ℝ)) (c := (21529588850986018613/21532500000000000000 : ℝ)) (alpha := (83159263069/107662500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21529588850986018613/21532500000000000000 : ℝ)*(X 0 1+X 2 1)+(83159263069/107662500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (4583/50000 : ℝ)) (hi := (17779/100000 : ℝ)) (c := (21529588850986018613/21532500000000000000 : ℝ)) (alpha := (83159263069/107662500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21529588850986018613/21532500000000000000 : ℝ)*(X 0 2+X 1 2)+(83159263069/107662500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4763/1024 : ℝ)) (lo := (4583/50000 : ℝ)) (hi := (17779/100000 : ℝ)) (c := (21529588850986018613/21532500000000000000 : ℝ)) (alpha := (83159263069/107662500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-848929843/5000000000 : ℝ)*X 0 0+(546586971/1000000000 : ℝ)*X 0 1+(2587446097/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355153769/10000000000 : ℝ)*X 1 0+(-1848102081/10000000000 : ℝ)*X 1 1+(5174892089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338788427/2500000000 : ℝ)*X 2 0+(5174892109/10000000000 : ℝ)*X 2 1+(-924051069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2104982269/5000000000 : ℝ)*X 0 0+(965804889/2500000000 : ℝ)*X 0 1+(916026811/2000000000 : ℝ)*X 0 2+(2104982269/5000000000 : ℝ)*X 1 0+(965804889/2500000000 : ℝ)*X 1 1+(916026811/2000000000 : ℝ)*X 1 2+(2104982269/5000000000 : ℝ)*X 2 0+(965804889/2500000000 : ℝ)*X 2 1+(916026811/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1697940239/10000000000 : ℝ)*X 0 0+(1035431591/2000000000 : ℝ)*X 0 1+(136589471/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41233117/78125000 : ℝ)*X 1 0+(-1559415571/10000000000 : ℝ)*X 1 1+(5463578653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105556769/200000000 : ℝ)*X 2 0+(5463579761/10000000000 : ℝ)*X 2 1+(-194926843/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4210162713/10000000000 : ℝ)*X 0 0+(182982049/400000000 : ℝ)*X 0 1+(773772707/2000000000 : ℝ)*X 0 2+(4210162713/10000000000 : ℝ)*X 1 0+(182982049/400000000 : ℝ)*X 1 1+(773772707/2000000000 : ℝ)*X 1 2+(4210162713/10000000000 : ℝ)*X 2 0+(182982049/400000000 : ℝ)*X 2 1+(773772707/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1612_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23856853889104813394156603/4078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224336397/20000000000000 : ℝ)*(base19) + (215753171/20000000000000 : ℝ)*(base23) + (504571/25000000000000 : ℝ)*(lower2) + (32596317/20000000000000 : ℝ)*(upper3) + (141137/125000000000 : ℝ)*(upper5) + (4718352934153/195312500000 : ℝ)*(major0) + (4718352934153/195312500000 : ℝ)*(major1) + (4718352934153/195312500000 : ℝ)*(major2) + (3436704563422461/100000000000000 : ℝ)*(sp0) + (1718357646959297/50000000000000 : ℝ)*(sp1) + (859178834208681/25000000000000 : ℝ)*(sp2) + (1394871435179621/100000000000000 : ℝ)*(sp3) + (5926089059/50000000000000 : ℝ)*(sp4) + (669849239/12500000000000 : ℝ)*(sp7) + (348719198493383/25000000000000 : ℝ)*(f.failure) + (3436716415600579/100000000000000 : ℝ)*(f.sum) + (46574272520209/21532500000000000000000000000 : ℝ)*base66 + (129186753723302687/33644531250000000000000000000000 : ℝ)*base67 + (703704405912132623/134578125000000000000000000000000 : ℝ)*base69 + (20068499805208937/33644531250000000000000000000000 : ℝ)*base71 + (61824244814029/21532500000000000000000000000 : ℝ)*base74 + (1089726911892507623/134578125000000000000000000000000 : ℝ)*base75 + (55379600258245999/67289062500000000000000000000000 : ℝ)*base77 + (10999349860191043/2102783203125000000000000000000 : ℝ)*base80 + (65848188398123/43065000000000000000000000000 : ℝ)*base82 + (33275879/2500000000000000000000 : ℝ)*base90 + (33275879/2500000000000000000000 : ℝ)*base92 + (33275879/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (178370720831575122562862743/59812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97328383/12500000000000 : ℝ)*(base19) + (690547907/100000000000000 : ℝ)*(base23) + (56177949/100000000000000 : ℝ)*(upper2) + (27944661/20000000000000 : ℝ)*(upper3) + (29683861/20000000000000 : ℝ)*(upper5) + (1227105325658989/50000000000000 : ℝ)*(major0) + (1227105325658989/50000000000000 : ℝ)*(major1) + (1227105325658989/50000000000000 : ℝ)*(major2) + (1283452759/25000000000000 : ℝ)*(sp1) + (3121582237/20000000000000 : ℝ)*(sp2) + (1745682131109777/50000000000000 : ℝ)*(sp4) + (1745679174890727/50000000000000 : ℝ)*(sp5) + (1745673981880231/50000000000000 : ℝ)*(sp6) + (1417056941010909/100000000000000 : ℝ)*(sp7) + (1417056941010909/100000000000000 : ℝ)*(f.failure) + (1745682131109777/50000000000000 : ℝ)*(f.sum) + (203607519513359/43065000000000000000000000000 : ℝ)*base66 + (8270204221376087257/1076625000000000000000000000000000 : ℝ)*base67 + (9119580513371087257/1076625000000000000000000000000000 : ℝ)*base69 + (7834153536622337257/1076625000000000000000000000000000 : ℝ)*base71 + (297856334168519/43065000000000000000000000000 : ℝ)*base74 + (9939583002173837257/1076625000000000000000000000000000 : ℝ)*base75 + (6059399569322837257/1076625000000000000000000000000000 : ℝ)*base77 + (7283050336500962257/1076625000000000000000000000000000 : ℝ)*base79 + (101062663688849/43065000000000000000000000000 : ℝ)*base82 + (4204483/10000000000000000000000 : ℝ)*base89 + (4204483/10000000000000000000000 : ℝ)*base91 + (4204483/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1612_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4583/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1612_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1612_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1612_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1612_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1612_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4763/1024 : ℝ) ≤ p) (hpb : p ≤ (4767/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (173190687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2579/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1612_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

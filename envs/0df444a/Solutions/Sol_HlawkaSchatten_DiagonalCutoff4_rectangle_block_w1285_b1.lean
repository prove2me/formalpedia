-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1285_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:22.407735+00:00
-- url     : https://prove2.me/submissions/4744f4cd-524a-4b10-922e-b6a37442e351

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
theorem support_rectangle_w1285_s3_0 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2091805107/10000000000 : ℝ)*x 0 + (5435133561/10000000000 : ℝ)*x 1 + (1306200679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091805107/10000000000 : ℝ)^4245 ≤ (397516933127/3125000000000 : ℝ)^3221 := by
    have hnat : (2091805107 : ℕ)^4245*3125000000000^3221 ≤ 397516933127^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091805107 10000000000 397516933127 3125000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435133561/10000000000 : ℝ)^4245 ≤ (44774415442989/100000000000000 : ℝ)^3221 := by
    have hnat : (5435133561 : ℕ)^4245*100000000000000^3221 ≤ 44774415442989^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435133561 10000000000 44774415442989 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306200679/2500000000 : ℝ)^4245 ≤ (42505042679857/100000000000000 : ℝ)^3221 := by
    have hnat : (1306200679 : ℕ)^4245*100000000000000^3221 ≤ 42505042679857^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306200679 2500000000 42505042679857 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2091805107/10000000000 : ℝ), (5435133561/10000000000 : ℝ), (1306200679/2500000000 : ℝ)] ![(397516933127/3125000000000 : ℝ), (44774415442989/100000000000000 : ℝ), (42505042679857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2091805107/10000000000 : ℝ)|^4245 ≤ (397516933127/3125000000000 : ℝ)^3221
        have hw : |(-2091805107/10000000000 : ℝ)|=(2091805107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435133561/10000000000 : ℝ)|^4245 ≤ (44774415442989/100000000000000 : ℝ)^3221
        have hw : |(5435133561/10000000000 : ℝ)|=(5435133561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306200679/2500000000 : ℝ)|^4245 ≤ (42505042679857/100000000000000 : ℝ)^3221
        have hw : |(1306200679/2500000000 : ℝ)|=(1306200679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s3_1 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354822609/10000000000 : ℝ)*x 0 + (-2199473007/10000000000 : ℝ)*x 1 + (1306200711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354822609/10000000000 : ℝ)^4245 ≤ (10976135172781/25000000000000 : ℝ)^3221 := by
    have hnat : (5354822609 : ℕ)^4245*25000000000000^3221 ≤ 10976135172781^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354822609 10000000000 10976135172781 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199473007/10000000000 : ℝ)^4245 ≤ (13590415243431/100000000000000 : ℝ)^3221 := by
    have hnat : (2199473007 : ℕ)^4245*100000000000000^3221 ≤ 13590415243431^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199473007 10000000000 13590415243431 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306200711/2500000000 : ℝ)^4245 ≤ (8501008810443/20000000000000 : ℝ)^3221 := by
    have hnat : (1306200711 : ℕ)^4245*20000000000000^3221 ≤ 8501008810443^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306200711 2500000000 8501008810443 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354822609/10000000000 : ℝ), (-2199473007/10000000000 : ℝ), (1306200711/2500000000 : ℝ)] ![(10976135172781/25000000000000 : ℝ), (13590415243431/100000000000000 : ℝ), (8501008810443/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354822609/10000000000 : ℝ)|^4245 ≤ (10976135172781/25000000000000 : ℝ)^3221
        have hw : |(5354822609/10000000000 : ℝ)|=(5354822609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2199473007/10000000000 : ℝ)|^4245 ≤ (13590415243431/100000000000000 : ℝ)^3221
        have hw : |(-2199473007/10000000000 : ℝ)|=(2199473007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306200711/2500000000 : ℝ)|^4245 ≤ (8501008810443/20000000000000 : ℝ)^3221
        have hw : |(1306200711/2500000000 : ℝ)|=(1306200711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s3_2 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669352847/1250000000 : ℝ)*x 0 + (5224802077/10000000000 : ℝ)*x 1 + (-439894759/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669352847/1250000000 : ℝ)^4245 ≤ (43904542495669/100000000000000 : ℝ)^3221 := by
    have hnat : (669352847 : ℕ)^4245*100000000000000^3221 ≤ 43904542495669^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669352847 1250000000 43904542495669 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5224802077/10000000000 : ℝ)^4245 ≤ (42505035828787/100000000000000 : ℝ)^3221 := by
    have hnat : (5224802077 : ℕ)^4245*100000000000000^3221 ≤ 42505035828787^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224802077 10000000000 42505035828787 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439894759/2000000000 : ℝ)^4245 ≤ (13590421660361/100000000000000 : ℝ)^3221 := by
    have hnat : (439894759 : ℕ)^4245*100000000000000^3221 ≤ 13590421660361^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439894759 2000000000 13590421660361 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669352847/1250000000 : ℝ), (5224802077/10000000000 : ℝ), (-439894759/2000000000 : ℝ)] ![(43904542495669/100000000000000 : ℝ), (42505035828787/100000000000000 : ℝ), (13590421660361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669352847/1250000000 : ℝ)|^4245 ≤ (43904542495669/100000000000000 : ℝ)^3221
        have hw : |(669352847/1250000000 : ℝ)|=(669352847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5224802077/10000000000 : ℝ)|^4245 ≤ (42505035828787/100000000000000 : ℝ)^3221
        have hw : |(5224802077/10000000000 : ℝ)|=(5224802077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-439894759/2000000000 : ℝ)|^4245 ≤ (13590421660361/100000000000000 : ℝ)^3221
        have hw : |(-439894759/2000000000 : ℝ)|=(439894759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s3_3 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (868054467/2000000000 : ℝ)*x 0 + (51622981/125000000 : ℝ)*x 1 + (456096339/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868054467/2000000000 : ℝ)^4245 ≤ (6657461468493/20000000000000 : ℝ)^3221 := by
    have hnat : (868054467 : ℕ)^4245*20000000000000^3221 ≤ 6657461468493^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868054467 2000000000 6657461468493 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51622981/125000000 : ℝ)^4245 ≤ (31176899998449/100000000000000 : ℝ)^3221 := by
    have hnat : (51622981 : ℕ)^4245*100000000000000^3221 ≤ 31176899998449^3221*125000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51622981 125000000 31176899998449 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456096339/1000000000 : ℝ)^4245 ≤ (35535792642793/100000000000000 : ℝ)^3221 := by
    have hnat : (456096339 : ℕ)^4245*100000000000000^3221 ≤ 35535792642793^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456096339 1000000000 35535792642793 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868054467/2000000000 : ℝ), (51622981/125000000 : ℝ), (456096339/1000000000 : ℝ)] ![(6657461468493/20000000000000 : ℝ), (31176899998449/100000000000000 : ℝ), (35535792642793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868054467/2000000000 : ℝ)|^4245 ≤ (6657461468493/20000000000000 : ℝ)^3221
        have hw : |(868054467/2000000000 : ℝ)|=(868054467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51622981/125000000 : ℝ)|^4245 ≤ (31176899998449/100000000000000 : ℝ)^3221
        have hw : |(51622981/125000000 : ℝ)|=(51622981/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(456096339/1000000000 : ℝ)|^4245 ≤ (35535792642793/100000000000000 : ℝ)^3221
        have hw : |(456096339/1000000000 : ℝ)|=(456096339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s3_4 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2091828183/10000000000 : ℝ)*x 0 + (209028517/400000000 : ℝ)*x 1 + (5434217617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091828183/10000000000 : ℝ)^4245 ≤ (12720726800831/100000000000000 : ℝ)^3221 := by
    have hnat : (2091828183 : ℕ)^4245*100000000000000^3221 ≤ 12720726800831^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091828183 10000000000 12720726800831 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209028517/400000000 : ℝ)^4245 ≤ (42514801800369/100000000000000 : ℝ)^3221 := by
    have hnat : (209028517 : ℕ)^4245*100000000000000^3221 ≤ 42514801800369^3221*400000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209028517 400000000 42514801800369 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434217617/10000000000 : ℝ)^4245 ≤ (44764471377833/100000000000000 : ℝ)^3221 := by
    have hnat : (5434217617 : ℕ)^4245*100000000000000^3221 ≤ 44764471377833^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434217617 10000000000 44764471377833 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2091828183/10000000000 : ℝ), (209028517/400000000 : ℝ), (5434217617/10000000000 : ℝ)] ![(12720726800831/100000000000000 : ℝ), (42514801800369/100000000000000 : ℝ), (44764471377833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2091828183/10000000000 : ℝ)|^4245 ≤ (12720726800831/100000000000000 : ℝ)^3221
        have hw : |(-2091828183/10000000000 : ℝ)|=(2091828183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209028517/400000000 : ℝ)|^4245 ≤ (42514801800369/100000000000000 : ℝ)^3221
        have hw : |(209028517/400000000 : ℝ)|=(209028517/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434217617/10000000000 : ℝ)|^4245 ≤ (44764471377833/100000000000000 : ℝ)^3221
        have hw : |(5434217617/10000000000 : ℝ)|=(5434217617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s3_5 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301015837/10000000000 : ℝ)*x 0 + (-1990058033/10000000000 : ℝ)*x 1 + (2717108779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301015837/10000000000 : ℝ)^4245 ≤ (21662026887543/50000000000000 : ℝ)^3221 := by
    have hnat : (5301015837 : ℕ)^4245*50000000000000^3221 ≤ 21662026887543^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301015837 10000000000 21662026887543 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1990058033/10000000000 : ℝ)^4245 ≤ (2382295094999/20000000000000 : ℝ)^3221 := by
    have hnat : (1990058033 : ℕ)^4245*20000000000000^3221 ≤ 2382295094999^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990058033 10000000000 2382295094999 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717108779/5000000000 : ℝ)^4245 ≤ (44764470737309/100000000000000 : ℝ)^3221 := by
    have hnat : (2717108779 : ℕ)^4245*100000000000000^3221 ≤ 44764470737309^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717108779 5000000000 44764470737309 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301015837/10000000000 : ℝ), (-1990058033/10000000000 : ℝ), (2717108779/5000000000 : ℝ)] ![(21662026887543/50000000000000 : ℝ), (2382295094999/20000000000000 : ℝ), (44764470737309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301015837/10000000000 : ℝ)|^4245 ≤ (21662026887543/50000000000000 : ℝ)^3221
        have hw : |(5301015837/10000000000 : ℝ)|=(5301015837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1990058033/10000000000 : ℝ)|^4245 ≤ (2382295094999/20000000000000 : ℝ)^3221
        have hw : |(-1990058033/10000000000 : ℝ)|=(1990058033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717108779/5000000000 : ℝ)|^4245 ≤ (44764470737309/100000000000000 : ℝ)^3221
        have hw : |(2717108779/5000000000 : ℝ)|=(2717108779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s3_6 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106020317/200000000 : ℝ)*x 0 + (217368701/400000000 : ℝ)*x 1 + (-1990058061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106020317/200000000 : ℝ)^4245 ≤ (4332405391511/10000000000000 : ℝ)^3221 := by
    have hnat : (106020317 : ℕ)^4245*10000000000000^3221 ≤ 4332405391511^3221*200000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106020317 200000000 4332405391511 10000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217368701/400000000 : ℝ)^4245 ≤ (44764470379049/100000000000000 : ℝ)^3221 := by
    have hnat : (217368701 : ℕ)^4245*100000000000000^3221 ≤ 44764470379049^3221*400000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217368701 400000000 44764470379049 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1990058061/10000000000 : ℝ)^4245 ≤ (11911475695869/100000000000000 : ℝ)^3221 := by
    have hnat : (1990058061 : ℕ)^4245*100000000000000^3221 ≤ 11911475695869^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990058061 10000000000 11911475695869 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106020317/200000000 : ℝ), (217368701/400000000 : ℝ), (-1990058061/10000000000 : ℝ)] ![(4332405391511/10000000000000 : ℝ), (44764470379049/100000000000000 : ℝ), (11911475695869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106020317/200000000 : ℝ)|^4245 ≤ (4332405391511/10000000000000 : ℝ)^3221
        have hw : |(106020317/200000000 : ℝ)|=(106020317/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217368701/400000000 : ℝ)|^4245 ≤ (44764470379049/100000000000000 : ℝ)^3221
        have hw : |(217368701/400000000 : ℝ)|=(217368701/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1990058061/10000000000 : ℝ)|^4245 ≤ (11911475695869/100000000000000 : ℝ)^3221
        have hw : |(-1990058061/10000000000 : ℝ)|=(1990058061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s3_7 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4340319011/10000000000 : ℝ)*x 0 + (911819459/2000000000 : ℝ)*x 1 + (2065858371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340319011/10000000000 : ℝ)^4245 ≤ (3328777912627/10000000000000 : ℝ)^3221 := by
    have hnat : (4340319011 : ℕ)^4245*10000000000000^3221 ≤ 3328777912627^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340319011 10000000000 3328777912627 10000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (911819459/2000000000 : ℝ)^4245 ≤ (4439579045129/12500000000000 : ℝ)^3221 := by
    have hnat : (911819459 : ℕ)^4245*12500000000000^3221 ≤ 4439579045129^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911819459 2000000000 4439579045129 12500000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065858371/5000000000 : ℝ)^4245 ≤ (31195588496427/100000000000000 : ℝ)^3221 := by
    have hnat : (2065858371 : ℕ)^4245*100000000000000^3221 ≤ 31195588496427^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065858371 5000000000 31195588496427 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340319011/10000000000 : ℝ), (911819459/2000000000 : ℝ), (2065858371/5000000000 : ℝ)] ![(3328777912627/10000000000000 : ℝ), (4439579045129/12500000000000 : ℝ), (31195588496427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340319011/10000000000 : ℝ)|^4245 ≤ (3328777912627/10000000000000 : ℝ)^3221
        have hw : |(4340319011/10000000000 : ℝ)|=(4340319011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(911819459/2000000000 : ℝ)|^4245 ≤ (4439579045129/12500000000000 : ℝ)^3221
        have hw : |(911819459/2000000000 : ℝ)|=(911819459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2065858371/5000000000 : ℝ)|^4245 ≤ (31195588496427/100000000000000 : ℝ)^3221
        have hw : |(2065858371/5000000000 : ℝ)|=(2065858371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1285_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9453/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5313/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3769/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (327/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9453/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (327/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9453/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (327/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9453/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (327/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9453/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (327/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9453/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (327/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9453/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9453/100000 : ℝ) ^ (1061/256 : ℝ) ≤ (5678275157208211/100000000000000000000 : ℝ) := by
    have hpowers : (9453/100000 : ℝ)^1061 ≤ (5678275157208211/100000000000000000000 : ℝ)^256 := by
      have hnat : (9453 : ℕ)^1061*100000000000000000000^256 ≤ 5678275157208211^256*100000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9453 100000 5678275157208211 100000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9453/100000 : ℝ)) (X := (5678275157208211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hpowhi : (327/2000 : ℝ) ^ (1061/256 : ℝ) ≤ (55004695688089373/100000000000000000000 : ℝ) := by
    have hpowers : (327/2000 : ℝ)^1061 ≤ (55004695688089373/100000000000000000000 : ℝ)^256 := by
      have hnat : (327 : ℕ)^1061*100000000000000000000^256 ≤ 55004695688089373^256*2000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        327 2000 55004695688089373 100000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (327/2000 : ℝ)) (X := (55004695688089373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005678275157208211/50000000000000000000 : ℝ) ≤ (625017125068551/625000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (50005678275157208211/50000000000000000000 : ℝ)^256 ≤ (625017125068551/625000000000000 : ℝ)^1061 := by
      have hnat : (50005678275157208211 : ℕ)^256*625000000000000^1061 ≤ 625017125068551^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005678275157208211 50000000000000000000 625017125068551 625000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625017125068551/625000000000000 : ℝ)) (X := (50005678275157208211/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253792685677831099/6250000000000000000 : ℝ) ≤ (625091489547531/625000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (6253792685677831099/6250000000000000000 : ℝ)^256 ≤ (625091489547531/625000000000000 : ℝ)^1061 := by
      have hnat : (6253792685677831099 : ℕ)^256*625000000000000^1061 ≤ 625091489547531^1061*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253792685677831099 6250000000000000000 625091489547531 625000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625091489547531/625000000000000 : ℝ)) (X := (6253792685677831099/6250000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50055004695688089373/50000000000000000000 : ℝ) ≤ (625165854026511/625000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (50055004695688089373/50000000000000000000 : ℝ)^256 ≤ (625165854026511/625000000000000 : ℝ)^1061 := by
      have hnat : (50055004695688089373 : ℕ)^256*625000000000000^1061 ≤ 625165854026511^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50055004695688089373 50000000000000000000 625165854026511 625000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625165854026511/625000000000000 : ℝ)) (X := (50055004695688089373/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5678275157208211/100000000000000000000 : ℝ) ≤ ((130585975053278799/130625000000000000 : ℝ)+2*(112673453/65312500000 : ℝ)*(9453/100000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (130585975053278799/130625000000000000 : ℝ)+2*(112673453/65312500000 : ℝ)*(9453/100000 : ℝ)=(625017125068551/625000000000000 : ℝ) by norm_num, show 1+2*(5678275157208211/100000000000000000000 : ℝ)=(50005678275157208211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(55004695688089373/100000000000000000000 : ℝ)+(5678275157208211/100000000000000000000 : ℝ) ≤ ((130585975053278799/130625000000000000 : ℝ)+(112673453/65312500000 : ℝ)*((327/2000 : ℝ)+(9453/100000 : ℝ)))^(1061/256 : ℝ) := by
    rw [show (130585975053278799/130625000000000000 : ℝ)+(112673453/65312500000 : ℝ)*((327/2000 : ℝ)+(9453/100000 : ℝ))=(625091489547531/625000000000000 : ℝ) by norm_num, show 1+(55004695688089373/100000000000000000000 : ℝ)+(5678275157208211/100000000000000000000 : ℝ)=(6253792685677831099/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(55004695688089373/100000000000000000000 : ℝ) ≤ ((130585975053278799/130625000000000000 : ℝ)+2*(112673453/65312500000 : ℝ)*(327/2000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (130585975053278799/130625000000000000 : ℝ)+2*(112673453/65312500000 : ℝ)*(327/2000 : ℝ)=(625165854026511/625000000000000 : ℝ) by norm_num, show 1+2*(55004695688089373/100000000000000000000 : ℝ)=(50055004695688089373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (130585975053278799/130625000000000000 : ℝ)*(X 1 0+X 2 0)+(112673453/65312500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (9453/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (130585975053278799/130625000000000000 : ℝ)) (alpha := (112673453/65312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (130585975053278799/130625000000000000 : ℝ)*(X 0 1+X 2 1)+(112673453/65312500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (9453/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (130585975053278799/130625000000000000 : ℝ)) (alpha := (112673453/65312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (130585975053278799/130625000000000000 : ℝ)*(X 0 2+X 1 2)+(112673453/65312500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (9453/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (130585975053278799/130625000000000000 : ℝ)) (alpha := (112673453/65312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2091805107/10000000000 : ℝ)*X 0 0+(5435133561/10000000000 : ℝ)*X 0 1+(1306200679/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354822609/10000000000 : ℝ)*X 1 0+(-2199473007/10000000000 : ℝ)*X 1 1+(1306200711/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669352847/1250000000 : ℝ)*X 2 0+(5224802077/10000000000 : ℝ)*X 2 1+(-439894759/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((868054467/2000000000 : ℝ)*X 0 0+(51622981/125000000 : ℝ)*X 0 1+(456096339/1000000000 : ℝ)*X 0 2+(868054467/2000000000 : ℝ)*X 1 0+(51622981/125000000 : ℝ)*X 1 1+(456096339/1000000000 : ℝ)*X 1 2+(868054467/2000000000 : ℝ)*X 2 0+(51622981/125000000 : ℝ)*X 2 1+(456096339/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2091828183/10000000000 : ℝ)*X 0 0+(209028517/400000000 : ℝ)*X 0 1+(5434217617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301015837/10000000000 : ℝ)*X 1 0+(-1990058033/10000000000 : ℝ)*X 1 1+(2717108779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106020317/200000000 : ℝ)*X 2 0+(217368701/400000000 : ℝ)*X 2 1+(-1990058061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4340319011/10000000000 : ℝ)*X 0 0+(911819459/2000000000 : ℝ)*X 0 1+(2065858371/5000000000 : ℝ)*X 0 2+(4340319011/10000000000 : ℝ)*X 1 0+(911819459/2000000000 : ℝ)*X 1 1+(2065858371/5000000000 : ℝ)*X 1 2+(4340319011/10000000000 : ℝ)*X 2 0+(911819459/2000000000 : ℝ)*X 2 1+(2065858371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16225364003254740134250381/1632812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (447778383/25000000000000 : ℝ)*(base19) + (2181336473/100000000000000 : ℝ)*(base23) + (2113329/6250000000000 : ℝ)*(lower2) + (71637563/12500000000000 : ℝ)*(upper3) + (163371183/100000000000000 : ℝ)*(lower4) + (1768502647993523/50000000000000 : ℝ)*(major0) + (1768502647993523/50000000000000 : ℝ)*(major1) + (1768502647993523/50000000000000 : ℝ)*(major2) + (4754449416581511/100000000000000 : ℝ)*(sp0) + (4754464006760873/100000000000000 : ℝ)*(sp1) + (1188615904134483/25000000000000 : ℝ)*(sp2) + (453032333127/19531250000 : ℝ)*(sp3) + (8190646447/50000000000000 : ℝ)*(sp4) + (945862697/5000000000000 : ℝ)*(sp7) + (2319544462864179/100000000000000 : ℝ)*(f.failure) + (950893159574881/20000000000000 : ℝ)*(f.sum) + (596432058283/209000000000000000000000000 : ℝ)*base65 + (19494457443312373/6531250000000000000000000000000 : ℝ)*base68 + (108139204302593623/6531250000000000000000000000000 : ℝ)*base70 + (75717862745937373/6531250000000000000000000000000 : ℝ)*base72 + (35984579669/209000000000000000000000000 : ℝ)*base74 + (85661419791406123/6531250000000000000000000000000 : ℝ)*base76 + (9550469467343877/6531250000000000000000000000000 : ℝ)*base77 + (45281394346031123/6531250000000000000000000000000 : ℝ)*base80 + (66795761157/52250000000000000000000000 : ℝ)*base82 + (6104407/5000000000000000000000 : ℝ)*base89 + (6104407/5000000000000000000000 : ℝ)*base91 + (6104407/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3814944007216782988306029/408203125000000000000000000000 : ℝ) := by norm_num
    linear_combination (133409127/6250000000000 : ℝ)*(base19) + (1120463781/50000000000000 : ℝ)*(base23) + (42678893/20000000000000 : ℝ)*(upper3) + (12040883/25000000000000 : ℝ)*(lower4) + (59447287/25000000000000 : ℝ)*(upper5) + (1783972477191023/50000000000000 : ℝ)*(major0) + (1783972477191023/50000000000000 : ℝ)*(major1) + (1783972477191023/50000000000000 : ℝ)*(major2) + (1749867701/5000000000000 : ℝ)*(sp1) + (17683976411/50000000000000 : ℝ)*(sp2) + (4796055112929761/100000000000000 : ℝ)*(sp4) + (4796017981029709/100000000000000 : ℝ)*(sp5) + (4796017504049377/100000000000000 : ℝ)*(sp6) + (2339834484310981/100000000000000 : ℝ)*(sp7) + (2339834484310981/100000000000000 : ℝ)*(f.failure) + (4796055112929761/100000000000000 : ℝ)*(f.sum) + (2290913357/5225000000000000000000000 : ℝ)*base65 + (81106077440771377/6531250000000000000000000000000 : ℝ)*base67 + (92563286851052627/6531250000000000000000000000000 : ℝ)*base69 + (102632149454646377/6531250000000000000000000000000 : ℝ)*base71 + (109647628469/20900000000000000000000000 : ℝ)*base74 + (27064881579646377/6531250000000000000000000000000 : ℝ)*base75 + (76839200105240127/6531250000000000000000000000000 : ℝ)*base77 + (81710333708083877/6531250000000000000000000000000 : ℝ)*base79 + (385310608897/209000000000000000000000000 : ℝ)*base81 + (37864127/5000000000000000000000 : ℝ)*base90 + (37864127/5000000000000000000000 : ℝ)*base92 + (37864127/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1285_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9453/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5313/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3769/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1285_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1285_s4_0 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2093802369/10000000000 : ℝ)*x 0 + (5419479687/10000000000 : ℝ)*x 1 + (5239147531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093802369/10000000000 : ℝ)^4245 ≤ (2547310231667/20000000000000 : ℝ)^3221 := by
    have hnat : (2093802369 : ℕ)^4245*20000000000000^3221 ≤ 2547310231667^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093802369 10000000000 2547310231667 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419479687/10000000000 : ℝ)^4245 ≤ (22302270214687/50000000000000 : ℝ)^3221 := by
    have hnat : (5419479687 : ℕ)^4245*50000000000000^3221 ≤ 22302270214687^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419479687 10000000000 22302270214687 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239147531/10000000000 : ℝ)^4245 ≤ (42658908393931/100000000000000 : ℝ)^3221 := by
    have hnat : (5239147531 : ℕ)^4245*100000000000000^3221 ≤ 42658908393931^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239147531 10000000000 42658908393931 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2093802369/10000000000 : ℝ), (5419479687/10000000000 : ℝ), (5239147531/10000000000 : ℝ)] ![(2547310231667/20000000000000 : ℝ), (22302270214687/50000000000000 : ℝ), (42658908393931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2093802369/10000000000 : ℝ)|^4245 ≤ (2547310231667/20000000000000 : ℝ)^3221
        have hw : |(-2093802369/10000000000 : ℝ)|=(2093802369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419479687/10000000000 : ℝ)|^4245 ≤ (22302270214687/50000000000000 : ℝ)^3221
        have hw : |(5419479687/10000000000 : ℝ)|=(5419479687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239147531/10000000000 : ℝ)|^4245 ≤ (42658908393931/100000000000000 : ℝ)^3221
        have hw : |(5239147531/10000000000 : ℝ)|=(5239147531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s4_1 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675435327/5000000000 : ℝ)*x 0 + (-2185808447/10000000000 : ℝ)*x 1 + (163723357/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675435327/5000000000 : ℝ)^4245 ≤ (21930921108747/50000000000000 : ℝ)^3221 := by
    have hnat : (2675435327 : ℕ)^4245*50000000000000^3221 ≤ 21930921108747^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675435327 5000000000 21930921108747 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185808447/10000000000 : ℝ)^4245 ≤ (13479250516109/100000000000000 : ℝ)^3221 := by
    have hnat : (2185808447 : ℕ)^4245*100000000000000^3221 ≤ 13479250516109^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185808447 10000000000 13479250516109 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163723357/312500000 : ℝ)^4245 ≤ (1706356289829/4000000000000 : ℝ)^3221 := by
    have hnat : (163723357 : ℕ)^4245*4000000000000^3221 ≤ 1706356289829^3221*312500000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163723357 312500000 1706356289829 4000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675435327/5000000000 : ℝ), (-2185808447/10000000000 : ℝ), (163723357/312500000 : ℝ)] ![(21930921108747/50000000000000 : ℝ), (13479250516109/100000000000000 : ℝ), (1706356289829/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675435327/5000000000 : ℝ)|^4245 ≤ (21930921108747/50000000000000 : ℝ)^3221
        have hw : |(2675435327/5000000000 : ℝ)|=(2675435327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2185808447/10000000000 : ℝ)|^4245 ≤ (13479250516109/100000000000000 : ℝ)^3221
        have hw : |(-2185808447/10000000000 : ℝ)|=(2185808447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163723357/312500000 : ℝ)|^4245 ≤ (1706356289829/4000000000000 : ℝ)^3221
        have hw : |(163723357/312500000 : ℝ)|=(163723357/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s4_2 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133771769/250000000 : ℝ)*x 0 + (1309786801/2500000000 : ℝ)*x 1 + (-2185808597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133771769/250000000 : ℝ)^4245 ≤ (350894746901/800000000000 : ℝ)^3221 := by
    have hnat : (133771769 : ℕ)^4245*800000000000^3221 ≤ 350894746901^3221*250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133771769 250000000 350894746901 800000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309786801/2500000000 : ℝ)^4245 ≤ (42658904884927/100000000000000 : ℝ)^3221 := by
    have hnat : (1309786801 : ℕ)^4245*100000000000000^3221 ≤ 42658904884927^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309786801 2500000000 42658904884927 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185808597/10000000000 : ℝ)^4245 ≤ (3369812933797/25000000000000 : ℝ)^3221 := by
    have hnat : (2185808597 : ℕ)^4245*25000000000000^3221 ≤ 3369812933797^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185808597 10000000000 3369812933797 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133771769/250000000 : ℝ), (1309786801/2500000000 : ℝ), (-2185808597/10000000000 : ℝ)] ![(350894746901/800000000000 : ℝ), (42658904884927/100000000000000 : ℝ), (3369812933797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133771769/250000000 : ℝ)|^4245 ≤ (350894746901/800000000000 : ℝ)^3221
        have hw : |(133771769/250000000 : ℝ)|=(133771769/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309786801/2500000000 : ℝ)|^4245 ≤ (42658904884927/100000000000000 : ℝ)^3221
        have hw : |(1309786801/2500000000 : ℝ)|=(1309786801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185808597/10000000000 : ℝ)|^4245 ≤ (3369812933797/25000000000000 : ℝ)^3221
        have hw : |(-2185808597/10000000000 : ℝ)|=(2185808597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s4_3 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1085369373/2500000000 : ℝ)*x 0 + (4160431571/10000000000 : ℝ)*x 1 + (1132516609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085369373/2500000000 : ℝ)^4245 ≤ (33299489142033/100000000000000 : ℝ)^3221 := by
    have hnat : (1085369373 : ℕ)^4245*100000000000000^3221 ≤ 33299489142033^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085369373 2500000000 33299489142033 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4160431571/10000000000 : ℝ)^4245 ≤ (6296326731317/20000000000000 : ℝ)^3221 := by
    have hnat : (4160431571 : ℕ)^4245*20000000000000^3221 ≤ 6296326731317^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160431571 10000000000 6296326731317 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132516609/2500000000 : ℝ)^4245 ≤ (35218877179771/100000000000000 : ℝ)^3221 := by
    have hnat : (1132516609 : ℕ)^4245*100000000000000^3221 ≤ 35218877179771^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132516609 2500000000 35218877179771 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085369373/2500000000 : ℝ), (4160431571/10000000000 : ℝ), (1132516609/2500000000 : ℝ)] ![(33299489142033/100000000000000 : ℝ), (6296326731317/20000000000000 : ℝ), (35218877179771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085369373/2500000000 : ℝ)|^4245 ≤ (33299489142033/100000000000000 : ℝ)^3221
        have hw : |(1085369373/2500000000 : ℝ)|=(1085369373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4160431571/10000000000 : ℝ)|^4245 ≤ (6296326731317/20000000000000 : ℝ)^3221
        have hw : |(4160431571/10000000000 : ℝ)|=(4160431571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132516609/2500000000 : ℝ)|^4245 ≤ (35218877179771/100000000000000 : ℝ)^3221
        have hw : |(1132516609/2500000000 : ℝ)|=(1132516609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s4_4 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418763311/2000000000 : ℝ)*x 0 + (5239817767/10000000000 : ℝ)*x 1 + (169337691/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418763311/2000000000 : ℝ)^4245 ≤ (12736664885327/100000000000000 : ℝ)^3221 := by
    have hnat : (418763311 : ℕ)^4245*100000000000000^3221 ≤ 12736664885327^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418763311 2000000000 12736664885327 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239817767/10000000000 : ℝ)^4245 ≤ (42666100774547/100000000000000 : ℝ)^3221 := by
    have hnat : (5239817767 : ℕ)^4245*100000000000000^3221 ≤ 42666100774547^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239817767 10000000000 42666100774547 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169337691/312500000 : ℝ)^4245 ≤ (44597234325787/100000000000000 : ℝ)^3221 := by
    have hnat : (169337691 : ℕ)^4245*100000000000000^3221 ≤ 44597234325787^3221*312500000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169337691 312500000 44597234325787 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418763311/2000000000 : ℝ), (5239817767/10000000000 : ℝ), (169337691/312500000 : ℝ)] ![(12736664885327/100000000000000 : ℝ), (42666100774547/100000000000000 : ℝ), (44597234325787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418763311/2000000000 : ℝ)|^4245 ≤ (12736664885327/100000000000000 : ℝ)^3221
        have hw : |(-418763311/2000000000 : ℝ)|=(418763311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239817767/10000000000 : ℝ)|^4245 ≤ (42666100774547/100000000000000 : ℝ)^3221
        have hw : |(5239817767/10000000000 : ℝ)|=(5239817767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169337691/312500000 : ℝ)|^4245 ≤ (44597234325787/100000000000000 : ℝ)^3221
        have hw : |(169337691/312500000 : ℝ)|=(169337691/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s4_5 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304742023/10000000000 : ℝ)*x 0 + (-2006149809/10000000000 : ℝ)*x 1 + (1354701447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304742023/10000000000 : ℝ)^4245 ≤ (43364193093991/100000000000000 : ℝ)^3221 := by
    have hnat : (5304742023 : ℕ)^4245*100000000000000^3221 ≤ 43364193093991^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304742023 10000000000 43364193093991 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006149809/10000000000 : ℝ)^4245 ≤ (12038576075761/100000000000000 : ℝ)^3221 := by
    have hnat : (2006149809 : ℕ)^4245*100000000000000^3221 ≤ 12038576075761^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006149809 10000000000 12038576075761 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354701447/2500000000 : ℝ)^4245 ≤ (11149307702877/25000000000000 : ℝ)^3221 := by
    have hnat : (1354701447 : ℕ)^4245*25000000000000^3221 ≤ 11149307702877^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354701447 2500000000 11149307702877 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304742023/10000000000 : ℝ), (-2006149809/10000000000 : ℝ), (1354701447/2500000000 : ℝ)] ![(43364193093991/100000000000000 : ℝ), (12038576075761/100000000000000 : ℝ), (11149307702877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304742023/10000000000 : ℝ)|^4245 ≤ (43364193093991/100000000000000 : ℝ)^3221
        have hw : |(5304742023/10000000000 : ℝ)|=(5304742023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2006149809/10000000000 : ℝ)|^4245 ≤ (12038576075761/100000000000000 : ℝ)^3221
        have hw : |(-2006149809/10000000000 : ℝ)|=(2006149809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354701447/2500000000 : ℝ)|^4245 ≤ (11149307702877/25000000000000 : ℝ)^3221
        have hw : |(1354701447/2500000000 : ℝ)|=(1354701447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s4_6 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212189691/400000000 : ℝ)*x 0 + (2709403081/5000000000 : ℝ)*x 1 + (-2006148953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212189691/400000000 : ℝ)^4245 ≤ (8672839161779/20000000000000 : ℝ)^3221 := by
    have hnat : (212189691 : ℕ)^4245*20000000000000^3221 ≤ 8672839161779^3221*400000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212189691 400000000 8672839161779 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709403081/5000000000 : ℝ)^4245 ≤ (22298617434057/50000000000000 : ℝ)^3221 := by
    have hnat : (2709403081 : ℕ)^4245*50000000000000^3221 ≤ 22298617434057^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709403081 5000000000 22298617434057 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006148953/10000000000 : ℝ)^4245 ≤ (12038569306013/100000000000000 : ℝ)^3221 := by
    have hnat : (2006148953 : ℕ)^4245*100000000000000^3221 ≤ 12038569306013^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006148953 10000000000 12038569306013 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212189691/400000000 : ℝ), (2709403081/5000000000 : ℝ), (-2006148953/10000000000 : ℝ)] ![(8672839161779/20000000000000 : ℝ), (22298617434057/50000000000000 : ℝ), (12038569306013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212189691/400000000 : ℝ)|^4245 ≤ (8672839161779/20000000000000 : ℝ)^3221
        have hw : |(212189691/400000000 : ℝ)|=(212189691/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709403081/5000000000 : ℝ)|^4245 ≤ (22298617434057/50000000000000 : ℝ)^3221
        have hw : |(2709403081/5000000000 : ℝ)|=(2709403081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2006148953/10000000000 : ℝ)|^4245 ≤ (12038569306013/100000000000000 : ℝ)^3221
        have hw : |(-2006148953/10000000000 : ℝ)|=(2006148953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s4_7 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2170753309/5000000000 : ℝ)*x 0 + (566086719/1250000000 : ℝ)*x 1 + (1040453061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170753309/5000000000 : ℝ)^4245 ≤ (16649891781351/50000000000000 : ℝ)^3221 := by
    have hnat : (2170753309 : ℕ)^4245*50000000000000^3221 ≤ 16649891781351^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170753309 5000000000 16649891781351 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566086719/1250000000 : ℝ)^4245 ≤ (7040962644387/20000000000000 : ℝ)^3221 := by
    have hnat : (566086719 : ℕ)^4245*20000000000000^3221 ≤ 7040962644387^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566086719 1250000000 7040962644387 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040453061/2500000000 : ℝ)^4245 ≤ (31495403201483/100000000000000 : ℝ)^3221 := by
    have hnat : (1040453061 : ℕ)^4245*100000000000000^3221 ≤ 31495403201483^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040453061 2500000000 31495403201483 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170753309/5000000000 : ℝ), (566086719/1250000000 : ℝ), (1040453061/2500000000 : ℝ)] ![(16649891781351/50000000000000 : ℝ), (7040962644387/20000000000000 : ℝ), (31495403201483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170753309/5000000000 : ℝ)|^4245 ≤ (16649891781351/50000000000000 : ℝ)^3221
        have hw : |(2170753309/5000000000 : ℝ)|=(2170753309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566086719/1250000000 : ℝ)|^4245 ≤ (7040962644387/20000000000000 : ℝ)^3221
        have hw : |(566086719/1250000000 : ℝ)|=(566086719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040453061/2500000000 : ℝ)|^4245 ≤ (31495403201483/100000000000000 : ℝ)^3221
        have hw : |(1040453061/2500000000 : ℝ)|=(1040453061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1285_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3769/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5313/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10933/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3769/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5313/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3769/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5313/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3769/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5313/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3769/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5313/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3769/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5313/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3769/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5313/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5313/50000 : ℝ) ^ (1061/256 : ℝ) ≤ (57628760068377/625000000000000000 : ℝ) := by
    have hpowers : (5313/50000 : ℝ)^1061 ≤ (57628760068377/625000000000000000 : ℝ)^256 := by
      have hnat : (5313 : ℕ)^1061*625000000000000000^256 ≤ 57628760068377^256*50000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5313 50000 57628760068377 625000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5313/50000 : ℝ)) (X := (57628760068377/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3769/25000 : ℝ) ^ (1061/256 : ℝ) ≤ (19649485642770567/50000000000000000000 : ℝ) := by
    have hpowers : (3769/25000 : ℝ)^1061 ≤ (19649485642770567/50000000000000000000 : ℝ)^256 := by
      have hnat : (3769 : ℕ)^1061*50000000000000000000^256 ≤ 19649485642770567^256*25000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3769 25000 19649485642770567 50000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3769/25000 : ℝ)) (X := (19649485642770567/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (312557628760068377/312500000000000000 : ℝ) ≤ (5000222460781839/5000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (312557628760068377/312500000000000000 : ℝ)^256 ≤ (5000222460781839/5000000000000000 : ℝ)^1061 := by
      have hnat : (312557628760068377 : ℕ)^256*5000000000000000^1061 ≤ 5000222460781839^1061*312500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312557628760068377 312500000000000000 5000222460781839 5000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000222460781839/5000000000000000 : ℝ)) (X := (312557628760068377/312500000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024259786448240727/50000000000000000000 : ℝ) ≤ (10001170473615267/10000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (50024259786448240727/50000000000000000000 : ℝ)^256 ≤ (10001170473615267/10000000000000000 : ℝ)^1061 := by
      have hnat : (50024259786448240727 : ℕ)^256*10000000000000000^1061 ≤ 10001170473615267^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024259786448240727 50000000000000000000 10001170473615267 10000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001170473615267/10000000000000000 : ℝ)) (X := (50024259786448240727/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019649485642770567/25000000000000000000 : ℝ) ≤ (1250237003208357/1250000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (25019649485642770567/25000000000000000000 : ℝ)^256 ≤ (1250237003208357/1250000000000000 : ℝ)^1061 := by
      have hnat : (25019649485642770567 : ℕ)^256*1250000000000000^1061 ≤ 1250237003208357^1061*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019649485642770567 25000000000000000000 1250237003208357 1250000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250237003208357/1250000000000000 : ℝ)) (X := (25019649485642770567/25000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(57628760068377/625000000000000000 : ℝ) ≤ ((5560820058594749709/5562500000000000000 : ℝ)+2*(725552051589/445000000000000 : ℝ)*(5313/50000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (5560820058594749709/5562500000000000000 : ℝ)+2*(725552051589/445000000000000 : ℝ)*(5313/50000 : ℝ)=(5000222460781839/5000000000000000 : ℝ) by norm_num, show 1+2*(57628760068377/625000000000000000 : ℝ)=(312557628760068377/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19649485642770567/50000000000000000000 : ℝ)+(57628760068377/625000000000000000 : ℝ) ≤ ((5560820058594749709/5562500000000000000 : ℝ)+(725552051589/445000000000000 : ℝ)*((3769/25000 : ℝ)+(5313/50000 : ℝ)))^(1061/256 : ℝ) := by
    rw [show (5560820058594749709/5562500000000000000 : ℝ)+(725552051589/445000000000000 : ℝ)*((3769/25000 : ℝ)+(5313/50000 : ℝ))=(10001170473615267/10000000000000000 : ℝ) by norm_num, show 1+(19649485642770567/50000000000000000000 : ℝ)+(57628760068377/625000000000000000 : ℝ)=(50024259786448240727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19649485642770567/50000000000000000000 : ℝ) ≤ ((5560820058594749709/5562500000000000000 : ℝ)+2*(725552051589/445000000000000 : ℝ)*(3769/25000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (5560820058594749709/5562500000000000000 : ℝ)+2*(725552051589/445000000000000 : ℝ)*(3769/25000 : ℝ)=(1250237003208357/1250000000000000 : ℝ) by norm_num, show 1+2*(19649485642770567/50000000000000000000 : ℝ)=(25019649485642770567/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5560820058594749709/5562500000000000000 : ℝ)*(X 1 0+X 2 0)+(725552051589/445000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (5313/50000 : ℝ)) (hi := (3769/25000 : ℝ)) (c := (5560820058594749709/5562500000000000000 : ℝ)) (alpha := (725552051589/445000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5560820058594749709/5562500000000000000 : ℝ)*(X 0 1+X 2 1)+(725552051589/445000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (5313/50000 : ℝ)) (hi := (3769/25000 : ℝ)) (c := (5560820058594749709/5562500000000000000 : ℝ)) (alpha := (725552051589/445000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5560820058594749709/5562500000000000000 : ℝ)*(X 0 2+X 1 2)+(725552051589/445000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (5313/50000 : ℝ)) (hi := (3769/25000 : ℝ)) (c := (5560820058594749709/5562500000000000000 : ℝ)) (alpha := (725552051589/445000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2093802369/10000000000 : ℝ)*X 0 0+(5419479687/10000000000 : ℝ)*X 0 1+(5239147531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675435327/5000000000 : ℝ)*X 1 0+(-2185808447/10000000000 : ℝ)*X 1 1+(163723357/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133771769/250000000 : ℝ)*X 2 0+(1309786801/2500000000 : ℝ)*X 2 1+(-2185808597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085369373/2500000000 : ℝ)*X 0 0+(4160431571/10000000000 : ℝ)*X 0 1+(1132516609/2500000000 : ℝ)*X 0 2+(1085369373/2500000000 : ℝ)*X 1 0+(4160431571/10000000000 : ℝ)*X 1 1+(1132516609/2500000000 : ℝ)*X 1 2+(1085369373/2500000000 : ℝ)*X 2 0+(4160431571/10000000000 : ℝ)*X 2 1+(1132516609/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-418763311/2000000000 : ℝ)*X 0 0+(5239817767/10000000000 : ℝ)*X 0 1+(169337691/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304742023/10000000000 : ℝ)*X 1 0+(-2006149809/10000000000 : ℝ)*X 1 1+(1354701447/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212189691/400000000 : ℝ)*X 2 0+(2709403081/5000000000 : ℝ)*X 2 1+(-2006148953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2170753309/5000000000 : ℝ)*X 0 0+(566086719/1250000000 : ℝ)*X 0 1+(1040453061/2500000000 : ℝ)*X 0 2+(2170753309/5000000000 : ℝ)*X 1 0+(566086719/1250000000 : ℝ)*X 1 1+(1040453061/2500000000 : ℝ)*X 1 2+(2170753309/5000000000 : ℝ)*X 2 0+(566086719/1250000000 : ℝ)*X 2 1+(1040453061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122058392080560768469757991/34765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70063817/5000000000000 : ℝ)*(base19) + (684822181/50000000000000 : ℝ)*(base23) + (30557227/10000000000000 : ℝ)*(upper3) + (75706693/100000000000000 : ℝ)*(upper4) + (25767571/50000000000000 : ℝ)*(upper5) + (515672453364221/12500000000000 : ℝ)*(major0) + (515672453364221/12500000000000 : ℝ)*(major1) + (515672453364221/12500000000000 : ℝ)*(major2) + (1386336473340273/25000000000000 : ℝ)*(sp0) + (5545361313956217/100000000000000 : ℝ)*(sp1) + (1109072269117639/20000000000000 : ℝ)*(sp2) + (2705382191762907/100000000000000 : ℝ)*(sp3) + (8410935733/50000000000000 : ℝ)*(sp4) + (2845960459/20000000000000 : ℝ)*(sp7) + (1352698210782601/50000000000000 : ℝ)*(f.failure) + (5545362715232557/100000000000000 : ℝ)*(f.sum) + (19187484520169/2781250000000000000000000000 : ℝ)*base65 + (699983245139469561/69531250000000000000000000000000 : ℝ)*base68 + (189274083722249189/69531250000000000000000000000000 : ℝ)*base69 + (442091099625374189/69531250000000000000000000000000 : ℝ)*base71 + (15210484239213/5562500000000000000000000000 : ℝ)*base73 + (198878368256624189/69531250000000000000000000000000 : ℝ)*base75 + (759117284705061689/69531250000000000000000000000000 : ℝ)*base77 + (580616745715217939/69531250000000000000000000000000 : ℝ)*base79 + (84226538374551/11125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4830667/2500000000000000000000 : ℝ)*base90 + (4830667/2500000000000000000000 : ℝ)*base92 + (4830667/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1466217006467691322262660271/278125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1607392007/100000000000000 : ℝ)*(base19) + (2247944727/100000000000000 : ℝ)*(base23) + (51017249/100000000000000 : ℝ)*(upper2) + (60413863/100000000000000 : ℝ)*(upper3) + (519540353408567/12500000000000 : ℝ)*(major0) + (519540353408567/12500000000000 : ℝ)*(major1) + (4156322827268537/100000000000000 : ℝ)*(major2) + (1377465051/5000000000000 : ℝ)*(sp1) + (59631125009/100000000000000 : ℝ)*(sp2) + (2645533741/50000000000000 : ℝ)*(sp3) + (1117391342601021/20000000000000 : ℝ)*(sp4) + (5586927556312077/100000000000000 : ℝ)*(sp5) + (5586894833935369/100000000000000 : ℝ)*(sp6) + (170355217171131/6250000000000 : ℝ)*(sp7) + (1362844382902789/50000000000000 : ℝ)*(f.failure) + (1117391342601021/20000000000000 : ℝ)*(f.sum) + (243459084207503/44500000000000000000000000000 : ℝ)*base66 + (565140974652692131/139062500000000000000000000000000 : ℝ)*base67 + (3324440333708094267/556250000000000000000000000000000 : ℝ)*base70 + (1516077074231682869/139062500000000000000000000000000 : ℝ)*base72 + (5390701504497/44500000000000000000000000000 : ℝ)*base73 + (2130879353983094267/556250000000000000000000000000000 : ℝ)*base76 + (983082477271449247/69531250000000000000000000000000 : ℝ)*base78 + (231917140122230497/69531250000000000000000000000000 : ℝ)*base80 + (14566326588801/5562500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (28913537/2500000000000000000000 : ℝ)*base89 + (28913537/2500000000000000000000 : ℝ)*base91 + (3913537/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1285_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3769/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5313/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10933/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1285_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1285_s5_0 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-130886153/625000000 : ℝ)*x 0 + (5416289549/10000000000 : ℝ)*x 1 + (2621045321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130886153/625000000 : ℝ)^4245 ≤ (6369783104483/50000000000000 : ℝ)^3221 := by
    have hnat : (130886153 : ℕ)^4245*50000000000000^3221 ≤ 6369783104483^3221*625000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130886153 625000000 6369783104483 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416289549/10000000000 : ℝ)^4245 ≤ (44569940335859/100000000000000 : ℝ)^3221 := by
    have hnat : (5416289549 : ℕ)^4245*100000000000000^3221 ≤ 44569940335859^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416289549 10000000000 44569940335859 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621045321/5000000000 : ℝ)^4245 ≤ (2668155839911/6250000000000 : ℝ)^3221 := by
    have hnat : (2621045321 : ℕ)^4245*6250000000000^3221 ≤ 2668155839911^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621045321 5000000000 2668155839911 6250000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130886153/625000000 : ℝ), (5416289549/10000000000 : ℝ), (2621045321/5000000000 : ℝ)] ![(6369783104483/50000000000000 : ℝ), (44569940335859/100000000000000 : ℝ), (2668155839911/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130886153/625000000 : ℝ)|^4245 ≤ (6369783104483/50000000000000 : ℝ)^3221
        have hw : |(-130886153/625000000 : ℝ)|=(130886153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416289549/10000000000 : ℝ)|^4245 ≤ (44569940335859/100000000000000 : ℝ)^3221
        have hw : |(5416289549/10000000000 : ℝ)|=(5416289549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621045321/5000000000 : ℝ)|^4245 ≤ (2668155839911/6250000000000 : ℝ)^3221
        have hw : |(2621045321/5000000000 : ℝ)|=(2621045321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s5_1 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535006287/1000000000 : ℝ)*x 0 + (-2182995123/10000000000 : ℝ)*x 1 + (1310522659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535006287/1000000000 : ℝ)^4245 ≤ (10963278958927/25000000000000 : ℝ)^3221 := by
    have hnat : (535006287 : ℕ)^4245*25000000000000^3221 ≤ 10963278958927^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535006287 1000000000 10963278958927 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182995123/10000000000 : ℝ)^4245 ≤ (6728195383019/50000000000000 : ℝ)^3221 := by
    have hnat : (2182995123 : ℕ)^4245*50000000000000^3221 ≤ 6728195383019^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182995123 10000000000 6728195383019 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310522659/2500000000 : ℝ)^4245 ≤ (42690493374179/100000000000000 : ℝ)^3221 := by
    have hnat : (1310522659 : ℕ)^4245*100000000000000^3221 ≤ 42690493374179^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310522659 2500000000 42690493374179 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535006287/1000000000 : ℝ), (-2182995123/10000000000 : ℝ), (1310522659/2500000000 : ℝ)] ![(10963278958927/25000000000000 : ℝ), (6728195383019/50000000000000 : ℝ), (42690493374179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535006287/1000000000 : ℝ)|^4245 ≤ (10963278958927/25000000000000 : ℝ)^3221
        have hw : |(535006287/1000000000 : ℝ)|=(535006287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182995123/10000000000 : ℝ)|^4245 ≤ (6728195383019/50000000000000 : ℝ)^3221
        have hw : |(-2182995123/10000000000 : ℝ)|=(2182995123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310522659/2500000000 : ℝ)|^4245 ≤ (42690493374179/100000000000000 : ℝ)^3221
        have hw : |(1310522659/2500000000 : ℝ)|=(1310522659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s5_2 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350062881/10000000000 : ℝ)*x 0 + (5242090633/10000000000 : ℝ)*x 1 + (-2182995113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350062881/10000000000 : ℝ)^4245 ≤ (43853115954537/100000000000000 : ℝ)^3221 := by
    have hnat : (5350062881 : ℕ)^4245*100000000000000^3221 ≤ 43853115954537^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350062881 10000000000 43853115954537 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242090633/10000000000 : ℝ)^4245 ≤ (2134524667099/5000000000000 : ℝ)^3221 := by
    have hnat : (5242090633 : ℕ)^4245*5000000000000^3221 ≤ 2134524667099^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242090633 10000000000 2134524667099 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182995113/10000000000 : ℝ)^4245 ≤ (13456390684799/100000000000000 : ℝ)^3221 := by
    have hnat : (2182995113 : ℕ)^4245*100000000000000^3221 ≤ 13456390684799^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182995113 10000000000 13456390684799 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350062881/10000000000 : ℝ), (5242090633/10000000000 : ℝ), (-2182995113/10000000000 : ℝ)] ![(43853115954537/100000000000000 : ℝ), (2134524667099/5000000000000 : ℝ), (13456390684799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350062881/10000000000 : ℝ)|^4245 ≤ (43853115954537/100000000000000 : ℝ)^3221
        have hw : |(5350062881/10000000000 : ℝ)|=(5350062881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242090633/10000000000 : ℝ)|^4245 ≤ (2134524667099/5000000000000 : ℝ)^3221
        have hw : |(5242090633/10000000000 : ℝ)|=(5242090633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182995113/10000000000 : ℝ)|^4245 ≤ (13456390684799/100000000000000 : ℝ)^3221
        have hw : |(-2182995113/10000000000 : ℝ)|=(2182995113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s5_3 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2170850467/5000000000 : ℝ)*x 0 + (4166689633/10000000000 : ℝ)*x 1 + (4523752149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170850467/5000000000 : ℝ)^4245 ≤ (1665087391269/5000000000000 : ℝ)^3221 := by
    have hnat : (2170850467 : ℕ)^4245*5000000000000^3221 ≤ 1665087391269^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170850467 5000000000 1665087391269 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4166689633/10000000000 : ℝ)^4245 ≤ (3943007169469/12500000000000 : ℝ)^3221 := by
    have hnat : (4166689633 : ℕ)^4245*12500000000000^3221 ≤ 3943007169469^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166689633 10000000000 3943007169469 12500000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523752149/10000000000 : ℝ)^4245 ≤ (17577097402441/50000000000000 : ℝ)^3221 := by
    have hnat : (4523752149 : ℕ)^4245*50000000000000^3221 ≤ 17577097402441^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523752149 10000000000 17577097402441 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170850467/5000000000 : ℝ), (4166689633/10000000000 : ℝ), (4523752149/10000000000 : ℝ)] ![(1665087391269/5000000000000 : ℝ), (3943007169469/12500000000000 : ℝ), (17577097402441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170850467/5000000000 : ℝ)|^4245 ≤ (1665087391269/5000000000000 : ℝ)^3221
        have hw : |(2170850467/5000000000 : ℝ)|=(2170850467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4166689633/10000000000 : ℝ)|^4245 ≤ (3943007169469/12500000000000 : ℝ)^3221
        have hw : |(4166689633/10000000000 : ℝ)|=(4166689633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523752149/10000000000 : ℝ)|^4245 ≤ (17577097402441/50000000000000 : ℝ)^3221
        have hw : |(4523752149/10000000000 : ℝ)|=(4523752149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s5_4 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1047095789/5000000000 : ℝ)*x 0 + (655339499/1250000000 : ℝ)*x 1 + (1083132187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047095789/5000000000 : ℝ)^4245 ≤ (12739671476169/100000000000000 : ℝ)^3221 := by
    have hnat : (1047095789 : ℕ)^4245*100000000000000^3221 ≤ 12739671476169^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047095789 5000000000 12739671476169 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655339499/1250000000 : ℝ)^4245 ≤ (21348602665657/50000000000000 : ℝ)^3221 := by
    have hnat : (655339499 : ℕ)^4245*50000000000000^3221 ≤ 21348602665657^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655339499 1250000000 21348602665657 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083132187/2000000000 : ℝ)^4245 ≤ (22281561590293/50000000000000 : ℝ)^3221 := by
    have hnat : (1083132187 : ℕ)^4245*50000000000000^3221 ≤ 22281561590293^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083132187 2000000000 22281561590293 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1047095789/5000000000 : ℝ), (655339499/1250000000 : ℝ), (1083132187/2000000000 : ℝ)] ![(12739671476169/100000000000000 : ℝ), (21348602665657/50000000000000 : ℝ), (22281561590293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1047095789/5000000000 : ℝ)|^4245 ≤ (12739671476169/100000000000000 : ℝ)^3221
        have hw : |(-1047095789/5000000000 : ℝ)|=(1047095789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655339499/1250000000 : ℝ)|^4245 ≤ (21348602665657/50000000000000 : ℝ)^3221
        have hw : |(655339499/1250000000 : ℝ)|=(655339499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083132187/2000000000 : ℝ)|^4245 ≤ (22281561590293/50000000000000 : ℝ)^3221
        have hw : |(1083132187/2000000000 : ℝ)|=(1083132187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s5_5 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061100627/2000000000 : ℝ)*x 0 + (-1004712413/5000000000 : ℝ)*x 1 + (5415660953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061100627/2000000000 : ℝ)^4245 ≤ (43372393067411/100000000000000 : ℝ)^3221 := by
    have hnat : (1061100627 : ℕ)^4245*100000000000000^3221 ≤ 43372393067411^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061100627 2000000000 43372393067411 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004712413/5000000000 : ℝ)^4245 ≤ (150806044267/1250000000000 : ℝ)^3221 := by
    have hnat : (1004712413 : ℕ)^4245*1250000000000^3221 ≤ 150806044267^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004712413 5000000000 150806044267 1250000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415660953/10000000000 : ℝ)^4245 ≤ (11140780843947/25000000000000 : ℝ)^3221 := by
    have hnat : (5415660953 : ℕ)^4245*25000000000000^3221 ≤ 11140780843947^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415660953 10000000000 11140780843947 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061100627/2000000000 : ℝ), (-1004712413/5000000000 : ℝ), (5415660953/10000000000 : ℝ)] ![(43372393067411/100000000000000 : ℝ), (150806044267/1250000000000 : ℝ), (11140780843947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061100627/2000000000 : ℝ)|^4245 ≤ (43372393067411/100000000000000 : ℝ)^3221
        have hw : |(1061100627/2000000000 : ℝ)|=(1061100627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1004712413/5000000000 : ℝ)|^4245 ≤ (150806044267/1250000000000 : ℝ)^3221
        have hw : |(-1004712413/5000000000 : ℝ)|=(1004712413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415660953/10000000000 : ℝ)|^4245 ≤ (11140780843947/25000000000000 : ℝ)^3221
        have hw : |(5415660953/10000000000 : ℝ)|=(5415660953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s5_6 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165796973/312500000 : ℝ)*x 0 + (5415660943/10000000000 : ℝ)*x 1 + (-1004712419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165796973/312500000 : ℝ)^4245 ≤ (8674478615637/20000000000000 : ℝ)^3221 := by
    have hnat : (165796973 : ℕ)^4245*20000000000000^3221 ≤ 8674478615637^3221*312500000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165796973 312500000 8674478615637 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415660943/10000000000 : ℝ)^4245 ≤ (22281561633671/50000000000000 : ℝ)^3221 := by
    have hnat : (5415660943 : ℕ)^4245*50000000000000^3221 ≤ 22281561633671^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415660943 10000000000 22281561633671 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004712419/5000000000 : ℝ)^4245 ≤ (1508060454539/12500000000000 : ℝ)^3221 := by
    have hnat : (1004712419 : ℕ)^4245*12500000000000^3221 ≤ 1508060454539^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004712419 5000000000 1508060454539 12500000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165796973/312500000 : ℝ), (5415660943/10000000000 : ℝ), (-1004712419/5000000000 : ℝ)] ![(8674478615637/20000000000000 : ℝ), (22281561633671/50000000000000 : ℝ), (1508060454539/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165796973/312500000 : ℝ)|^4245 ≤ (8674478615637/20000000000000 : ℝ)^3221
        have hw : |(165796973/312500000 : ℝ)|=(165796973/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415660943/10000000000 : ℝ)|^4245 ≤ (22281561633671/50000000000000 : ℝ)^3221
        have hw : |(5415660943/10000000000 : ℝ)|=(5415660943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004712419/5000000000 : ℝ)|^4245 ≤ (1508060454539/12500000000000 : ℝ)^3221
        have hw : |(-1004712419/5000000000 : ℝ)|=(1004712419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s5_7 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434172787/1000000000 : ℝ)*x 0 + (904494069/2000000000 : ℝ)*x 1 + (4167977971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434172787/1000000000 : ℝ)^4245 ≤ (3330202011283/10000000000000 : ℝ)^3221 := by
    have hnat : (434172787 : ℕ)^4245*10000000000000^3221 ≤ 3330202011283^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434172787 1000000000 3330202011283 10000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904494069/2000000000 : ℝ)^4245 ≤ (1757053387377/5000000000000 : ℝ)^3221 := by
    have hnat : (904494069 : ℕ)^4245*5000000000000^3221 ≤ 1757053387377^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904494069 2000000000 1757053387377 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4167977971/10000000000 : ℝ)^4245 ≤ (31556912132287/100000000000000 : ℝ)^3221 := by
    have hnat : (4167977971 : ℕ)^4245*100000000000000^3221 ≤ 31556912132287^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167977971 10000000000 31556912132287 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434172787/1000000000 : ℝ), (904494069/2000000000 : ℝ), (4167977971/10000000000 : ℝ)] ![(3330202011283/10000000000000 : ℝ), (1757053387377/5000000000000 : ℝ), (31556912132287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434172787/1000000000 : ℝ)|^4245 ≤ (3330202011283/10000000000000 : ℝ)^3221
        have hw : |(434172787/1000000000 : ℝ)|=(434172787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904494069/2000000000 : ℝ)|^4245 ≤ (1757053387377/5000000000000 : ℝ)^3221
        have hw : |(904494069/2000000000 : ℝ)|=(904494069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4167977971/10000000000 : ℝ)|^4245 ≤ (31556912132287/100000000000000 : ℝ)^3221
        have hw : |(4167977971/10000000000 : ℝ)|=(4167977971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1285_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10933/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2749/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7341/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10933/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10933/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10933/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10933/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10933/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10933/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10933/100000 : ℝ) ^ (1061/256 : ℝ) ≤ (10375885936016027/100000000000000000000 : ℝ) := by
    have hpowers : (10933/100000 : ℝ)^1061 ≤ (10375885936016027/100000000000000000000 : ℝ)^256 := by
      have hnat : (10933 : ℕ)^1061*100000000000000000000^256 ≤ 10375885936016027^256*100000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10933 100000 10375885936016027 100000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10933/100000 : ℝ)) (X := (10375885936016027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (1061/256 : ℝ) ≤ (35884799042754011/100000000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^1061 ≤ (35884799042754011/100000000000000000000 : ℝ)^256 := by
      have hnat : (14749 : ℕ)^1061*100000000000000000000^256 ≤ 35884799042754011^256*100000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 35884799042754011 100000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (35884799042754011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010375885936016027/50000000000000000000 : ℝ) ≤ (10000500663094621/10000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (50010375885936016027/50000000000000000000 : ℝ)^256 ≤ (10000500663094621/10000000000000000 : ℝ)^1061 := by
      have hnat : (50010375885936016027 : ℕ)^256*10000000000000000^1061 ≤ 10000500663094621^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010375885936016027 50000000000000000000 10000500663094621 10000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000500663094621/10000000000000000 : ℝ)) (X := (50010375885936016027/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023130342489385019/50000000000000000000 : ℝ) ≤ (2500278997586891/2500000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (50023130342489385019/50000000000000000000 : ℝ)^256 ≤ (2500278997586891/2500000000000000 : ℝ)^1061 := by
      have hnat : (50023130342489385019 : ℕ)^256*2500000000000000^1061 ≤ 2500278997586891^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023130342489385019 50000000000000000000 2500278997586891 2500000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500278997586891/2500000000000000 : ℝ)) (X := (50023130342489385019/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035884799042754011/50000000000000000000 : ℝ) ≤ (10001731317600507/10000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (50035884799042754011/50000000000000000000 : ℝ)^256 ≤ (10001731317600507/10000000000000000 : ℝ)^1061 := by
      have hnat : (50035884799042754011 : ℕ)^256*10000000000000000^1061 ≤ 10001731317600507^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035884799042754011 50000000000000000000 10001731317600507 10000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001731317600507/10000000000000000 : ℝ)) (X := (50035884799042754011/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10375885936016027/100000000000000000000 : ℝ) ≤ ((19074227892328111049/19080000000000000000 : ℝ)+2*(615327252943/381600000000000 : ℝ)*(10933/100000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (19074227892328111049/19080000000000000000 : ℝ)+2*(615327252943/381600000000000 : ℝ)*(10933/100000 : ℝ)=(10000500663094621/10000000000000000 : ℝ) by norm_num, show 1+2*(10375885936016027/100000000000000000000 : ℝ)=(50010375885936016027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35884799042754011/100000000000000000000 : ℝ)+(10375885936016027/100000000000000000000 : ℝ) ≤ ((19074227892328111049/19080000000000000000 : ℝ)+(615327252943/381600000000000 : ℝ)*((14749/100000 : ℝ)+(10933/100000 : ℝ)))^(1061/256 : ℝ) := by
    rw [show (19074227892328111049/19080000000000000000 : ℝ)+(615327252943/381600000000000 : ℝ)*((14749/100000 : ℝ)+(10933/100000 : ℝ))=(2500278997586891/2500000000000000 : ℝ) by norm_num, show 1+(35884799042754011/100000000000000000000 : ℝ)+(10375885936016027/100000000000000000000 : ℝ)=(50023130342489385019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35884799042754011/100000000000000000000 : ℝ) ≤ ((19074227892328111049/19080000000000000000 : ℝ)+2*(615327252943/381600000000000 : ℝ)*(14749/100000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (19074227892328111049/19080000000000000000 : ℝ)+2*(615327252943/381600000000000 : ℝ)*(14749/100000 : ℝ)=(10001731317600507/10000000000000000 : ℝ) by norm_num, show 1+2*(35884799042754011/100000000000000000000 : ℝ)=(50035884799042754011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19074227892328111049/19080000000000000000 : ℝ)*(X 1 0+X 2 0)+(615327252943/381600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (10933/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (19074227892328111049/19080000000000000000 : ℝ)) (alpha := (615327252943/381600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19074227892328111049/19080000000000000000 : ℝ)*(X 0 1+X 2 1)+(615327252943/381600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (10933/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (19074227892328111049/19080000000000000000 : ℝ)) (alpha := (615327252943/381600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19074227892328111049/19080000000000000000 : ℝ)*(X 0 2+X 1 2)+(615327252943/381600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (10933/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (19074227892328111049/19080000000000000000 : ℝ)) (alpha := (615327252943/381600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-130886153/625000000 : ℝ)*X 0 0+(5416289549/10000000000 : ℝ)*X 0 1+(2621045321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535006287/1000000000 : ℝ)*X 1 0+(-2182995123/10000000000 : ℝ)*X 1 1+(1310522659/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350062881/10000000000 : ℝ)*X 2 0+(5242090633/10000000000 : ℝ)*X 2 1+(-2182995113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170850467/5000000000 : ℝ)*X 0 0+(4166689633/10000000000 : ℝ)*X 0 1+(4523752149/10000000000 : ℝ)*X 0 2+(2170850467/5000000000 : ℝ)*X 1 0+(4166689633/10000000000 : ℝ)*X 1 1+(4523752149/10000000000 : ℝ)*X 1 2+(2170850467/5000000000 : ℝ)*X 2 0+(4166689633/10000000000 : ℝ)*X 2 1+(4523752149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1047095789/5000000000 : ℝ)*X 0 0+(655339499/1250000000 : ℝ)*X 0 1+(1083132187/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061100627/2000000000 : ℝ)*X 1 0+(-1004712413/5000000000 : ℝ)*X 1 1+(5415660953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165796973/312500000 : ℝ)*X 2 0+(5415660943/10000000000 : ℝ)*X 2 1+(-1004712419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434172787/1000000000 : ℝ)*X 0 0+(904494069/2000000000 : ℝ)*X 0 1+(4167977971/10000000000 : ℝ)*X 0 2+(434172787/1000000000 : ℝ)*X 1 0+(904494069/2000000000 : ℝ)*X 1 1+(4167977971/10000000000 : ℝ)*X 1 2+(434172787/1000000000 : ℝ)*X 2 0+(904494069/2000000000 : ℝ)*X 2 1+(4167977971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48572396800025900160047559/13250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161933893/25000000000000 : ℝ)*(base19) + (311498161/50000000000000 : ℝ)*(base23) + (3910061/20000000000000 : ℝ)*(lower2) + (3830313/6250000000000 : ℝ)*(upper3) + (24181919/50000000000000 : ℝ)*(upper5) + (533827153808973/12500000000000 : ℝ)*(major0) + (533827153808973/12500000000000 : ℝ)*(major1) + (533827153808973/12500000000000 : ℝ)*(major2) + (5740578039820309/100000000000000 : ℝ)*(sp0) + (1435147854631467/25000000000000 : ℝ)*(sp1) + (2870295721632559/50000000000000 : ℝ)*(sp2) + (1400317967941207/50000000000000 : ℝ)*(sp3) + (14026441131/100000000000000 : ℝ)*(sp4) + (6336605001/100000000000000 : ℝ)*(sp7) + (560128454497483/20000000000000 : ℝ)*(f.failure) + (17939350207067/312500000000 : ℝ)*(f.sum) + (914961074231/265000000000000000000000000 : ℝ)*base65 + (185535952682934147/26500000000000000000000000000000 : ℝ)*base68 + (177933290037065853/26500000000000000000000000000000 : ℝ)*base69 + (64381840391934147/26500000000000000000000000000000 : ℝ)*base72 + (156629142653/33125000000000000000000000 : ℝ)*base74 + (197365173865434147/26500000000000000000000000000000 : ℝ)*base76 + (30794781038934147/26500000000000000000000000000000 : ℝ)*base78 + (21468211640565853/26500000000000000000000000000000 : ℝ)*base79 + (56600163661/16562500000000000000000000 : ℝ)*base81 + (3527439/1000000000000000000000 : ℝ)*base89 + (3527439/1000000000000000000000 : ℝ)*base91 + (3527439/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42571902873585309124680569/10600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (720859627/100000000000000 : ℝ)*(base19) + (779837431/100000000000000 : ℝ)*(base23) + (16852001/20000000000000 : ℝ)*(upper3) + (3551607/12500000000000 : ℝ)*(lower4) + (45148431/50000000000000 : ℝ)*(upper5) + (430156081796557/10000000000000 : ℝ)*(major0) + (430156081796557/10000000000000 : ℝ)*(major1) + (430156081796557/10000000000000 : ℝ)*(major2) + (924029057/6250000000000 : ℝ)*(sp1) + (3825134171/25000000000000 : ℝ)*(sp2) + (2891093315723127/50000000000000 : ℝ)*(sp4) + (1156434225224343/20000000000000 : ℝ)*(sp5) + (5782170551072139/100000000000000 : ℝ)*(sp6) + (1410467435305487/50000000000000 : ℝ)*(sp7) + (1410467435305487/50000000000000 : ℝ)*(f.failure) + (2891093315723127/50000000000000 : ℝ)*(f.sum) + (138925534493/1908000000000000000000000000 : ℝ)*base66 + (344136630366008293/190800000000000000000000000000000 : ℝ)*base67 + (2036547711370791707/190800000000000000000000000000000 : ℝ)*base70 + (139908250958408293/190800000000000000000000000000000 : ℝ)*base71 + (5565901553539/1908000000000000000000000000 : ℝ)*base73 + (1135164393849608293/190800000000000000000000000000000 : ℝ)*base75 + (857152059354008293/190800000000000000000000000000000 : ℝ)*base77 + (627560848288791707/190800000000000000000000000000000 : ℝ)*base80 + (1387391635411/1908000000000000000000000000 : ℝ)*base81 + (13165571/2500000000000000000000 : ℝ)*base89 + (13165571/2500000000000000000000 : ℝ)*base91 + (13165571/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1285_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10933/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1285_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1285_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9453/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1285_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1285_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1285_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9453/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1285_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

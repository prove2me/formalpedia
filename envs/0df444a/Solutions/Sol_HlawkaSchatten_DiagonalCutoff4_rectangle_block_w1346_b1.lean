-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1346_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:06:01.52548+00:00
-- url     : https://prove2.me/submissions/708fc5f5-89e9-47b0-9a70-279e75b3c4f0

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
theorem support_rectangle_w1346_s3_0 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-509700397/2500000000 : ℝ)*x 0 + (5426657577/10000000000 : ℝ)*x 1 + (1046340511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509700397/2500000000 : ℝ)^2153 ≤ (3103391694569/25000000000000 : ℝ)^1641 := by
    have hnat : (509700397 : ℕ)^2153*25000000000000^1641 ≤ 3103391694569^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509700397 2500000000 3103391694569 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426657577/10000000000 : ℝ)^2153 ≤ (1121102310007/2500000000000 : ℝ)^1641 := by
    have hnat : (5426657577 : ℕ)^2153*2500000000000^1641 ≤ 1121102310007^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426657577 10000000000 1121102310007 2500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046340511/2000000000 : ℝ)^2153 ≤ (534279259951/1250000000000 : ℝ)^1641 := by
    have hnat : (1046340511 : ℕ)^2153*1250000000000^1641 ≤ 534279259951^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046340511 2000000000 534279259951 1250000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-509700397/2500000000 : ℝ), (5426657577/10000000000 : ℝ), (1046340511/2000000000 : ℝ)] ![(3103391694569/25000000000000 : ℝ), (1121102310007/2500000000000 : ℝ), (534279259951/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-509700397/2500000000 : ℝ)|^2153 ≤ (3103391694569/25000000000000 : ℝ)^1641
        have hw : |(-509700397/2500000000 : ℝ)|=(509700397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426657577/10000000000 : ℝ)|^2153 ≤ (1121102310007/2500000000000 : ℝ)^1641
        have hw : |(5426657577/10000000000 : ℝ)|=(5426657577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046340511/2000000000 : ℝ)|^2153 ≤ (534279259951/1250000000000 : ℝ)^1641
        have hw : |(1046340511/2000000000 : ℝ)|=(1046340511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s3_1 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676270637/5000000000 : ℝ)*x 0 + (-534607047/2500000000 : ℝ)*x 1 + (2615851137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676270637/5000000000 : ℝ)^2153 ≤ (8808448611383/20000000000000 : ℝ)^1641 := by
    have hnat : (2676270637 : ℕ)^2153*20000000000000^1641 ≤ 8808448611383^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676270637 5000000000 8808448611383 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534607047/2500000000 : ℝ)^2153 ≤ (13215419142933/100000000000000 : ℝ)^1641 := by
    have hnat : (534607047 : ℕ)^2153*100000000000000^1641 ≤ 13215419142933^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534607047 2500000000 13215419142933 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615851137/5000000000 : ℝ)^2153 ≤ (21371168892033/50000000000000 : ℝ)^1641 := by
    have hnat : (2615851137 : ℕ)^2153*50000000000000^1641 ≤ 21371168892033^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615851137 5000000000 21371168892033 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676270637/5000000000 : ℝ), (-534607047/2500000000 : ℝ), (2615851137/5000000000 : ℝ)] ![(8808448611383/20000000000000 : ℝ), (13215419142933/100000000000000 : ℝ), (21371168892033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676270637/5000000000 : ℝ)|^2153 ≤ (8808448611383/20000000000000 : ℝ)^1641
        have hw : |(2676270637/5000000000 : ℝ)|=(2676270637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534607047/2500000000 : ℝ)|^2153 ≤ (13215419142933/100000000000000 : ℝ)^1641
        have hw : |(-534607047/2500000000 : ℝ)|=(534607047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615851137/5000000000 : ℝ)|^2153 ≤ (21371168892033/50000000000000 : ℝ)^1641
        have hw : |(2615851137/5000000000 : ℝ)|=(2615851137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s3_2 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5352541199/10000000000 : ℝ)*x 0 + (653962731/1250000000 : ℝ)*x 1 + (-534607213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352541199/10000000000 : ℝ)^2153 ≤ (2752640140453/6250000000000 : ℝ)^1641 := by
    have hnat : (5352541199 : ℕ)^2153*6250000000000^1641 ≤ 2752640140453^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352541199 10000000000 2752640140453 6250000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653962731/1250000000 : ℝ)^2153 ≤ (4274233321781/10000000000000 : ℝ)^1641 := by
    have hnat : (653962731 : ℕ)^2153*10000000000000^1641 ≤ 4274233321781^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653962731 1250000000 4274233321781 10000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534607213/2500000000 : ℝ)^2153 ≤ (1651928065843/12500000000000 : ℝ)^1641 := by
    have hnat : (534607213 : ℕ)^2153*12500000000000^1641 ≤ 1651928065843^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534607213 2500000000 1651928065843 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352541199/10000000000 : ℝ), (653962731/1250000000 : ℝ), (-534607213/2500000000 : ℝ)] ![(2752640140453/6250000000000 : ℝ), (4274233321781/10000000000000 : ℝ), (1651928065843/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352541199/10000000000 : ℝ)|^2153 ≤ (2752640140453/6250000000000 : ℝ)^1641
        have hw : |(5352541199/10000000000 : ℝ)|=(5352541199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653962731/1250000000 : ℝ)|^2153 ≤ (4274233321781/10000000000000 : ℝ)^1641
        have hw : |(653962731/1250000000 : ℝ)|=(653962731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534607213/2500000000 : ℝ)|^2153 ≤ (1651928065843/12500000000000 : ℝ)^1641
        have hw : |(-534607213/2500000000 : ℝ)|=(534607213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s3_3 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4324534699/10000000000 : ℝ)*x 0 + (824912029/2000000000 : ℝ)*x 1 + (4533522909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324534699/10000000000 : ℝ)^2153 ≤ (16646414486169/50000000000000 : ℝ)^1641 := by
    have hnat : (4324534699 : ℕ)^2153*50000000000000^1641 ≤ 16646414486169^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324534699 10000000000 16646414486169 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824912029/2000000000 : ℝ)^2153 ≤ (31287696476167/100000000000000 : ℝ)^1641 := by
    have hnat : (824912029 : ℕ)^2153*100000000000000^1641 ≤ 31287696476167^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824912029 2000000000 31287696476167 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4533522909/10000000000 : ℝ)^2153 ≤ (1416778981429/4000000000000 : ℝ)^1641 := by
    have hnat : (4533522909 : ℕ)^2153*4000000000000^1641 ≤ 1416778981429^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533522909 10000000000 1416778981429 4000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324534699/10000000000 : ℝ), (824912029/2000000000 : ℝ), (4533522909/10000000000 : ℝ)] ![(16646414486169/50000000000000 : ℝ), (31287696476167/100000000000000 : ℝ), (1416778981429/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324534699/10000000000 : ℝ)|^2153 ≤ (16646414486169/50000000000000 : ℝ)^1641
        have hw : |(4324534699/10000000000 : ℝ)|=(4324534699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(824912029/2000000000 : ℝ)|^2153 ≤ (31287696476167/100000000000000 : ℝ)^1641
        have hw : |(824912029/2000000000 : ℝ)|=(824912029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4533522909/10000000000 : ℝ)|^2153 ≤ (1416778981429/4000000000000 : ℝ)^1641
        have hw : |(4533522909/10000000000 : ℝ)|=(4533522909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s3_4 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-509705169/2500000000 : ℝ)*x 0 + (20439503/39062500 : ℝ)*x 1 + (2712921229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509705169/2500000000 : ℝ)^2153 ≤ (6206859630059/50000000000000 : ℝ)^1641 := by
    have hnat : (509705169 : ℕ)^2153*50000000000000^1641 ≤ 6206859630059^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509705169 2500000000 6206859630059 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20439503/39062500 : ℝ)^2153 ≤ (5343878200971/12500000000000 : ℝ)^1641 := by
    have hnat : (20439503 : ℕ)^2153*12500000000000^1641 ≤ 5343878200971^1641*39062500^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20439503 39062500 5343878200971 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712921229/5000000000 : ℝ)^2153 ≤ (44835255110247/100000000000000 : ℝ)^1641 := by
    have hnat : (2712921229 : ℕ)^2153*100000000000000^1641 ≤ 44835255110247^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712921229 5000000000 44835255110247 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-509705169/2500000000 : ℝ), (20439503/39062500 : ℝ), (2712921229/5000000000 : ℝ)] ![(6206859630059/50000000000000 : ℝ), (5343878200971/12500000000000 : ℝ), (44835255110247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-509705169/2500000000 : ℝ)|^2153 ≤ (6206859630059/50000000000000 : ℝ)^1641
        have hw : |(-509705169/2500000000 : ℝ)|=(509705169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20439503/39062500 : ℝ)|^2153 ≤ (5343878200971/12500000000000 : ℝ)^1641
        have hw : |(20439503/39062500 : ℝ)|=(20439503/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712921229/5000000000 : ℝ)|^2153 ≤ (44835255110247/100000000000000 : ℝ)^1641
        have hw : |(2712921229/5000000000 : ℝ)|=(2712921229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s3_5 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662787619/1250000000 : ℝ)*x 0 + (-486071983/2500000000 : ℝ)*x 1 + (5425842453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662787619/1250000000 : ℝ)^2153 ≤ (271879168431/625000000000 : ℝ)^1641 := by
    have hnat : (662787619 : ℕ)^2153*625000000000^1641 ≤ 271879168431^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662787619 1250000000 271879168431 625000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486071983/2500000000 : ℝ)^2153 ≤ (466563119087/4000000000000 : ℝ)^1641 := by
    have hnat : (486071983 : ℕ)^2153*4000000000000^1641 ≤ 466563119087^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486071983 2500000000 466563119087 4000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425842453/10000000000 : ℝ)^2153 ≤ (44835255056039/100000000000000 : ℝ)^1641 := by
    have hnat : (5425842453 : ℕ)^2153*100000000000000^1641 ≤ 44835255056039^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425842453 10000000000 44835255056039 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662787619/1250000000 : ℝ), (-486071983/2500000000 : ℝ), (5425842453/10000000000 : ℝ)] ![(271879168431/625000000000 : ℝ), (466563119087/4000000000000 : ℝ), (44835255056039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662787619/1250000000 : ℝ)|^2153 ≤ (271879168431/625000000000 : ℝ)^1641
        have hw : |(662787619/1250000000 : ℝ)|=(662787619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486071983/2500000000 : ℝ)|^2153 ≤ (466563119087/4000000000000 : ℝ)^1641
        have hw : |(-486071983/2500000000 : ℝ)|=(486071983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425842453/10000000000 : ℝ)|^2153 ≤ (44835255056039/100000000000000 : ℝ)^1641
        have hw : |(5425842453/10000000000 : ℝ)|=(5425842453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s3_6 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651150361/5000000000 : ℝ)*x 0 + (1356460653/2500000000 : ℝ)*x 1 + (-486072007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651150361/5000000000 : ℝ)^2153 ≤ (21750332236639/50000000000000 : ℝ)^1641 := by
    have hnat : (2651150361 : ℕ)^2153*50000000000000^1641 ≤ 21750332236639^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651150361 5000000000 21750332236639 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356460653/2500000000 : ℝ)^2153 ≤ (5604407097479/12500000000000 : ℝ)^1641 := by
    have hnat : (1356460653 : ℕ)^2153*12500000000000^1641 ≤ 5604407097479^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356460653 2500000000 5604407097479 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (486072007/2500000000 : ℝ)^2153 ≤ (11664078732783/100000000000000 : ℝ)^1641 := by
    have hnat : (486072007 : ℕ)^2153*100000000000000^1641 ≤ 11664078732783^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486072007 2500000000 11664078732783 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651150361/5000000000 : ℝ), (1356460653/2500000000 : ℝ), (-486072007/2500000000 : ℝ)] ![(21750332236639/50000000000000 : ℝ), (5604407097479/12500000000000 : ℝ), (11664078732783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651150361/5000000000 : ℝ)|^2153 ≤ (21750332236639/50000000000000 : ℝ)^1641
        have hw : |(2651150361/5000000000 : ℝ)|=(2651150361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356460653/2500000000 : ℝ)|^2153 ≤ (5604407097479/12500000000000 : ℝ)^1641
        have hw : |(1356460653/2500000000 : ℝ)|=(1356460653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-486072007/2500000000 : ℝ)|^2153 ≤ (11664078732783/100000000000000 : ℝ)^1641
        have hw : |(-486072007/2500000000 : ℝ)|=(486072007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s3_7 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2162287047/5000000000 : ℝ)*x 0 + (566477883/1250000000 : ℝ)*x 1 + (4126270683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162287047/5000000000 : ℝ)^2153 ≤ (6658645377133/20000000000000 : ℝ)^1641 := by
    have hnat : (2162287047 : ℕ)^2153*20000000000000^1641 ≤ 6658645377133^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162287047 5000000000 6658645377133 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566477883/1250000000 : ℝ)^2153 ≤ (8850512856577/25000000000000 : ℝ)^1641 := by
    have hnat : (566477883 : ℕ)^2153*25000000000000^1641 ≤ 8850512856577^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566477883 1250000000 8850512856577 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4126270683/10000000000 : ℝ)^2153 ≤ (3130472167601/10000000000000 : ℝ)^1641 := by
    have hnat : (4126270683 : ℕ)^2153*10000000000000^1641 ≤ 3130472167601^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126270683 10000000000 3130472167601 10000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162287047/5000000000 : ℝ), (566477883/1250000000 : ℝ), (4126270683/10000000000 : ℝ)] ![(6658645377133/20000000000000 : ℝ), (8850512856577/25000000000000 : ℝ), (3130472167601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162287047/5000000000 : ℝ)|^2153 ≤ (6658645377133/20000000000000 : ℝ)^1641
        have hw : |(2162287047/5000000000 : ℝ)|=(2162287047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566477883/1250000000 : ℝ)|^2153 ≤ (8850512856577/25000000000000 : ℝ)^1641
        have hw : |(566477883/1250000000 : ℝ)|=(566477883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4126270683/10000000000 : ℝ)|^2153 ≤ (3130472167601/10000000000000 : ℝ)^1641
        have hw : |(4126270683/10000000000 : ℝ)|=(4126270683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1346_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2011/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4939/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (68/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7503/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2011/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4939/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2011/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4939/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2011/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4939/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2011/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4939/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2011/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4939/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2011/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4939/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4939/50000 : ℝ) ^ (4305/1024 : ℝ) ≤ (5935898467818939/100000000000000000000 : ℝ) := by
    have hpowers : (4939/50000 : ℝ)^4305 ≤ (5935898467818939/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4939 : ℕ)^4305*100000000000000000000^1024 ≤ 5935898467818939^1024*50000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4939 50000 5935898467818939 100000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4939/50000 : ℝ)) (X := (5935898467818939/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2011/12500 : ℝ) ^ (4305/1024 : ℝ) ≤ (23068750120276893/50000000000000000000 : ℝ) := by
    have hpowers : (2011/12500 : ℝ)^4305 ≤ (23068750120276893/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2011 : ℕ)^4305*50000000000000000000^1024 ≤ 23068750120276893^1024*12500^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2011 12500 23068750120276893 50000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2011/12500 : ℝ)) (X := (23068750120276893/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005935898467818939/50000000000000000000 : ℝ) ≤ (2500070593322499/2500000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (50005935898467818939/50000000000000000000 : ℝ)^1024 ≤ (2500070593322499/2500000000000000 : ℝ)^4305 := by
      have hnat : (50005935898467818939 : ℕ)^1024*2500000000000000^4305 ≤ 2500070593322499^4305*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005935898467818939 50000000000000000000 2500070593322499 2500000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070593322499/2500000000000000 : ℝ)) (X := (50005935898467818939/50000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002082935948334909/4000000000000000000 : ℝ) ≤ (10001238387510189/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (4002082935948334909/4000000000000000000 : ℝ)^1024 ≤ (10001238387510189/10000000000000000 : ℝ)^4305 := by
      have hnat : (4002082935948334909 : ℕ)^1024*10000000000000000^4305 ≤ 10001238387510189^4305*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002082935948334909 4000000000000000000 10001238387510189 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001238387510189/10000000000000000 : ℝ)) (X := (4002082935948334909/4000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25023068750120276893/25000000000000000000 : ℝ) ≤ (5001097200865191/5000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (25023068750120276893/25000000000000000000 : ℝ)^1024 ≤ (5001097200865191/5000000000000000 : ℝ)^4305 := by
      have hnat : (25023068750120276893 : ℕ)^1024*5000000000000000^4305 ≤ 5001097200865191^4305*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25023068750120276893 25000000000000000000 5001097200865191 5000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001097200865191/5000000000000000 : ℝ)) (X := (25023068750120276893/25000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5935898467818939/100000000000000000000 : ℝ) ≤ ((5173572210099728521/5175000000000000000 : ℝ)+2*(318671406731/207000000000000 : ℝ)*(4939/50000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (5173572210099728521/5175000000000000000 : ℝ)+2*(318671406731/207000000000000 : ℝ)*(4939/50000 : ℝ)=(2500070593322499/2500000000000000 : ℝ) by norm_num, show 1+2*(5935898467818939/100000000000000000000 : ℝ)=(50005935898467818939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23068750120276893/50000000000000000000 : ℝ)+(5935898467818939/100000000000000000000 : ℝ) ≤ ((5173572210099728521/5175000000000000000 : ℝ)+(318671406731/207000000000000 : ℝ)*((2011/12500 : ℝ)+(4939/50000 : ℝ)))^(4305/1024 : ℝ) := by
    rw [show (5173572210099728521/5175000000000000000 : ℝ)+(318671406731/207000000000000 : ℝ)*((2011/12500 : ℝ)+(4939/50000 : ℝ))=(10001238387510189/10000000000000000 : ℝ) by norm_num, show 1+(23068750120276893/50000000000000000000 : ℝ)+(5935898467818939/100000000000000000000 : ℝ)=(4002082935948334909/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23068750120276893/50000000000000000000 : ℝ) ≤ ((5173572210099728521/5175000000000000000 : ℝ)+2*(318671406731/207000000000000 : ℝ)*(2011/12500 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (5173572210099728521/5175000000000000000 : ℝ)+2*(318671406731/207000000000000 : ℝ)*(2011/12500 : ℝ)=(5001097200865191/5000000000000000 : ℝ) by norm_num, show 1+2*(23068750120276893/50000000000000000000 : ℝ)=(25023068750120276893/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5173572210099728521/5175000000000000000 : ℝ)*(X 1 0+X 2 0)+(318671406731/207000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (4939/50000 : ℝ)) (hi := (2011/12500 : ℝ)) (c := (5173572210099728521/5175000000000000000 : ℝ)) (alpha := (318671406731/207000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5173572210099728521/5175000000000000000 : ℝ)*(X 0 1+X 2 1)+(318671406731/207000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (4939/50000 : ℝ)) (hi := (2011/12500 : ℝ)) (c := (5173572210099728521/5175000000000000000 : ℝ)) (alpha := (318671406731/207000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5173572210099728521/5175000000000000000 : ℝ)*(X 0 2+X 1 2)+(318671406731/207000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (4939/50000 : ℝ)) (hi := (2011/12500 : ℝ)) (c := (5173572210099728521/5175000000000000000 : ℝ)) (alpha := (318671406731/207000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-509700397/2500000000 : ℝ)*X 0 0+(5426657577/10000000000 : ℝ)*X 0 1+(1046340511/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676270637/5000000000 : ℝ)*X 1 0+(-534607047/2500000000 : ℝ)*X 1 1+(2615851137/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352541199/10000000000 : ℝ)*X 2 0+(653962731/1250000000 : ℝ)*X 2 1+(-534607213/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324534699/10000000000 : ℝ)*X 0 0+(824912029/2000000000 : ℝ)*X 0 1+(4533522909/10000000000 : ℝ)*X 0 2+(4324534699/10000000000 : ℝ)*X 1 0+(824912029/2000000000 : ℝ)*X 1 1+(4533522909/10000000000 : ℝ)*X 1 2+(4324534699/10000000000 : ℝ)*X 2 0+(824912029/2000000000 : ℝ)*X 2 1+(4533522909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-509705169/2500000000 : ℝ)*X 0 0+(20439503/39062500 : ℝ)*X 0 1+(2712921229/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662787619/1250000000 : ℝ)*X 1 0+(-486071983/2500000000 : ℝ)*X 1 1+(5425842453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651150361/5000000000 : ℝ)*X 2 0+(1356460653/2500000000 : ℝ)*X 2 1+(-486072007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162287047/5000000000 : ℝ)*X 0 0+(566477883/1250000000 : ℝ)*X 0 1+(4126270683/10000000000 : ℝ)*X 0 2+(2162287047/5000000000 : ℝ)*X 1 0+(566477883/1250000000 : ℝ)*X 1 1+(4126270683/10000000000 : ℝ)*X 1 2+(2162287047/5000000000 : ℝ)*X 2 0+(566477883/1250000000 : ℝ)*X 2 1+(4126270683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168188003677941020592179993/28750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (983667767/100000000000000 : ℝ)*(base19) + (316182433/25000000000000 : ℝ)*(base23) + (64981171/20000000000000 : ℝ)*(upper3) + (41071613/20000000000000 : ℝ)*(lower4) + (3452257/20000000000000 : ℝ)*(upper5) + (3787312468932833/100000000000000 : ℝ)*(major0) + (3787312468932833/100000000000000 : ℝ)*(major1) + (3787312468932833/100000000000000 : ℝ)*(major2) + (5129402960931863/100000000000000 : ℝ)*(sp0) + (160293811789503/3125000000000 : ℝ)*(sp1) + (2564699211176311/50000000000000 : ℝ)*(sp2) + (1222607474410089/50000000000000 : ℝ)*(sp3) + (3273849509/100000000000000 : ℝ)*(sp6) + (6833113031/100000000000000 : ℝ)*(sp7) + (244522178193321/10000000000000 : ℝ)*(f.failure) + (5129402960931863/100000000000000 : ℝ)*(f.sum) + (48528092266723/10350000000000000000000000000 : ℝ)*base65 + (429523148686777223/57500000000000000000000000000000 : ℝ)*base68 + (630831177399277223/57500000000000000000000000000000 : ℝ)*base70 + (658720730149277223/57500000000000000000000000000000 : ℝ)*base72 + (91128300477823/10350000000000000000000000000 : ℝ)*base73 + (314796476891777223/57500000000000000000000000000000 : ℝ)*base76 + (291434936039277223/57500000000000000000000000000000 : ℝ)*base78 + (941436851934277223/57500000000000000000000000000000 : ℝ)*base80 + (62651465386273/10350000000000000000000000000 : ℝ)*base81 + (243511/62500000000000000000 : ℝ)*base89 + (243511/62500000000000000000 : ℝ)*base91 + (243511/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (151865902020604310088772411/14375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1982114969/100000000000000 : ℝ)*(base19) + (472926271/25000000000000 : ℝ)*(base23) + (201716597/100000000000000 : ℝ)*(upper3) + (79381709/100000000000000 : ℝ)*(lower4) + (237898749/100000000000000 : ℝ)*(upper5) + (1909570169812091/50000000000000 : ℝ)*(major0) + (1909570169812091/50000000000000 : ℝ)*(major1) + (1909570169812091/50000000000000 : ℝ)*(major2) + (36177352221/100000000000000 : ℝ)*(sp1) + (8628705049/25000000000000 : ℝ)*(sp2) + (5172509355380543/100000000000000 : ℝ)*(sp4) + (5172471195913353/100000000000000 : ℝ)*(sp5) + (5172472948855263/100000000000000 : ℝ)*(sp6) + (493154194343/20000000000 : ℝ)*(sp7) + (493154194343/20000000000 : ℝ)*(f.failure) + (5172509355380543/100000000000000 : ℝ)*(f.sum) + (7080685088579/5175000000000000000000000000 : ℝ)*base66 + (169153171295958621/28750000000000000000000000000000 : ℝ)*base68 + (293336113058458621/28750000000000000000000000000000 : ℝ)*base70 + (303796855643458621/28750000000000000000000000000000 : ℝ)*base72 + (3218559425279/5175000000000000000000000000 : ℝ)*base74 + (56583622667208621/28750000000000000000000000000000 : ℝ)*base76 + (251649337443458621/28750000000000000000000000000000 : ℝ)*base78 + (15643010320958621/28750000000000000000000000000000 : ℝ)*base80 + (12370858398179/5175000000000000000000000000 : ℝ)*base82 + (613/125000000000000000 : ℝ)*base89 + (613/125000000000000000 : ℝ)*base91 + (613/125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1346_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2011/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4939/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7503/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1346_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1346_s4_0 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2040228519/10000000000 : ℝ)*x 0 + (5414991043/10000000000 : ℝ)*x 1 + (5242432091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040228519/10000000000 : ℝ)^2153 ≤ (496998673861/4000000000000 : ℝ)^1641 := by
    have hnat : (2040228519 : ℕ)^2153*4000000000000^1641 ≤ 496998673861^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040228519 10000000000 496998673861 4000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414991043/10000000000 : ℝ)^2153 ≤ (4471764661179/10000000000000 : ℝ)^1641 := by
    have hnat : (5414991043 : ℕ)^2153*10000000000000^1641 ≤ 4471764661179^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414991043 10000000000 4471764661179 10000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242432091/10000000000 : ℝ)^2153 ≤ (4285738652741/10000000000000 : ℝ)^1641 := by
    have hnat : (5242432091 : ℕ)^2153*10000000000000^1641 ≤ 4285738652741^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242432091 10000000000 4285738652741 10000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2040228519/10000000000 : ℝ), (5414991043/10000000000 : ℝ), (5242432091/10000000000 : ℝ)] ![(496998673861/4000000000000 : ℝ), (4471764661179/10000000000000 : ℝ), (4285738652741/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2040228519/10000000000 : ℝ)|^2153 ≤ (496998673861/4000000000000 : ℝ)^1641
        have hw : |(-2040228519/10000000000 : ℝ)|=(2040228519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414991043/10000000000 : ℝ)|^2153 ≤ (4471764661179/10000000000000 : ℝ)^1641
        have hw : |(5414991043/10000000000 : ℝ)|=(5414991043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242432091/10000000000 : ℝ)|^2153 ≤ (4285738652741/10000000000000 : ℝ)^1641
        have hw : |(5242432091/10000000000 : ℝ)|=(5242432091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s4_1 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674783151/5000000000 : ℝ)*x 0 + (-2128192097/10000000000 : ℝ)*x 1 + (1048486393/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674783151/5000000000 : ℝ)^2153 ≤ (44010129377099/100000000000000 : ℝ)^1641 := by
    have hnat : (2674783151 : ℕ)^2153*100000000000000^1641 ≤ 44010129377099^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674783151 5000000000 44010129377099 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128192097/10000000000 : ℝ)^2153 ≤ (13132485436707/100000000000000 : ℝ)^1641 := by
    have hnat : (2128192097 : ℕ)^2153*100000000000000^1641 ≤ 13132485436707^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128192097 10000000000 13132485436707 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048486393/2000000000 : ℝ)^2153 ≤ (42857385175963/100000000000000 : ℝ)^1641 := by
    have hnat : (1048486393 : ℕ)^2153*100000000000000^1641 ≤ 42857385175963^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048486393 2000000000 42857385175963 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674783151/5000000000 : ℝ), (-2128192097/10000000000 : ℝ), (1048486393/2000000000 : ℝ)] ![(44010129377099/100000000000000 : ℝ), (13132485436707/100000000000000 : ℝ), (42857385175963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674783151/5000000000 : ℝ)|^2153 ≤ (44010129377099/100000000000000 : ℝ)^1641
        have hw : |(2674783151/5000000000 : ℝ)|=(2674783151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2128192097/10000000000 : ℝ)|^2153 ≤ (13132485436707/100000000000000 : ℝ)^1641
        have hw : |(-2128192097/10000000000 : ℝ)|=(2128192097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048486393/2000000000 : ℝ)|^2153 ≤ (42857385175963/100000000000000 : ℝ)^1641
        have hw : |(1048486393/2000000000 : ℝ)|=(1048486393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s4_2 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349566653/10000000000 : ℝ)*x 0 + (5242431817/10000000000 : ℝ)*x 1 + (-133011989/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349566653/10000000000 : ℝ)^2153 ≤ (550126664571/1250000000000 : ℝ)^1641 := by
    have hnat : (5349566653 : ℕ)^2153*1250000000000^1641 ≤ 550126664571^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349566653 10000000000 550126664571 1250000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242431817/10000000000 : ℝ)^2153 ≤ (857147671771/2000000000000 : ℝ)^1641 := by
    have hnat : (5242431817 : ℕ)^2153*2000000000000^1641 ≤ 857147671771^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242431817 10000000000 857147671771 2000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133011989/625000000 : ℝ)^2153 ≤ (6566241613247/50000000000000 : ℝ)^1641 := by
    have hnat : (133011989 : ℕ)^2153*50000000000000^1641 ≤ 6566241613247^1641*625000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133011989 625000000 6566241613247 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349566653/10000000000 : ℝ), (5242431817/10000000000 : ℝ), (-133011989/625000000 : ℝ)] ![(550126664571/1250000000000 : ℝ), (857147671771/2000000000000 : ℝ), (6566241613247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349566653/10000000000 : ℝ)|^2153 ≤ (550126664571/1250000000000 : ℝ)^1641
        have hw : |(5349566653/10000000000 : ℝ)|=(5349566653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242431817/10000000000 : ℝ)|^2153 ≤ (857147671771/2000000000000 : ℝ)^1641
        have hw : |(5242431817/10000000000 : ℝ)|=(5242431817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133011989/625000000 : ℝ)|^2153 ≤ (6566241613247/50000000000000 : ℝ)^1641
        have hw : |(-133011989/625000000 : ℝ)|=(133011989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s4_3 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (865080489/2000000000 : ℝ)*x 0 + (1036985833/2500000000 : ℝ)*x 1 + (2254962527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865080489/2000000000 : ℝ)^2153 ≤ (6660318798731/20000000000000 : ℝ)^1641 := by
    have hnat : (865080489 : ℕ)^2153*20000000000000^1641 ≤ 6660318798731^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865080489 2000000000 6660318798731 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036985833/2500000000 : ℝ)^2153 ≤ (6304124555523/20000000000000 : ℝ)^1641 := by
    have hnat : (1036985833 : ℕ)^2153*20000000000000^1641 ≤ 6304124555523^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036985833 2500000000 6304124555523 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254962527/5000000000 : ℝ)^2153 ≤ (17588891607799/50000000000000 : ℝ)^1641 := by
    have hnat : (2254962527 : ℕ)^2153*50000000000000^1641 ≤ 17588891607799^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254962527 5000000000 17588891607799 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865080489/2000000000 : ℝ), (1036985833/2500000000 : ℝ), (2254962527/5000000000 : ℝ)] ![(6660318798731/20000000000000 : ℝ), (6304124555523/20000000000000 : ℝ), (17588891607799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865080489/2000000000 : ℝ)|^2153 ≤ (6660318798731/20000000000000 : ℝ)^1641
        have hw : |(865080489/2000000000 : ℝ)|=(865080489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036985833/2500000000 : ℝ)|^2153 ≤ (6304124555523/20000000000000 : ℝ)^1641
        have hw : |(1036985833/2500000000 : ℝ)|=(1036985833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254962527/5000000000 : ℝ)|^2153 ≤ (17588891607799/50000000000000 : ℝ)^1641
        have hw : |(2254962527/5000000000 : ℝ)|=(2254962527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s4_4 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-510060493/2500000000 : ℝ)*x 0 + (41944539/80000000 : ℝ)*x 1 + (2707176101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510060493/2500000000 : ℝ)^2153 ≤ (12425074337367/100000000000000 : ℝ)^1641 := by
    have hnat : (510060493 : ℕ)^2153*100000000000000^1641 ≤ 12425074337367^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510060493 2500000000 12425074337367 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41944539/80000000 : ℝ)^2153 ≤ (42864200563769/100000000000000 : ℝ)^1641 := by
    have hnat : (41944539 : ℕ)^2153*100000000000000^1641 ≤ 42864200563769^1641*80000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41944539 80000000 42864200563769 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707176101/5000000000 : ℝ)^2153 ≤ (8942145018501/20000000000000 : ℝ)^1641 := by
    have hnat : (2707176101 : ℕ)^2153*20000000000000^1641 ≤ 8942145018501^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707176101 5000000000 8942145018501 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-510060493/2500000000 : ℝ), (41944539/80000000 : ℝ), (2707176101/5000000000 : ℝ)] ![(12425074337367/100000000000000 : ℝ), (42864200563769/100000000000000 : ℝ), (8942145018501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-510060493/2500000000 : ℝ)|^2153 ≤ (12425074337367/100000000000000 : ℝ)^1641
        have hw : |(-510060493/2500000000 : ℝ)|=(510060493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41944539/80000000 : ℝ)|^2153 ≤ (42864200563769/100000000000000 : ℝ)^1641
        have hw : |(41944539/80000000 : ℝ)|=(41944539/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707176101/5000000000 : ℝ)|^2153 ≤ (8942145018501/20000000000000 : ℝ)^1641
        have hw : |(2707176101/5000000000 : ℝ)|=(2707176101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s4_5 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326274637/2500000000 : ℝ)*x 0 + (-978136029/5000000000 : ℝ)*x 1 + (2707176009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326274637/2500000000 : ℝ)^2153 ≤ (8706156457221/20000000000000 : ℝ)^1641 := by
    have hnat : (1326274637 : ℕ)^2153*20000000000000^1641 ≤ 8706156457221^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326274637 2500000000 8706156457221 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978136029/5000000000 : ℝ)^2153 ≤ (11758494599787/100000000000000 : ℝ)^1641 := by
    have hnat : (978136029 : ℕ)^2153*100000000000000^1641 ≤ 11758494599787^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978136029 5000000000 11758494599787 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707176009/5000000000 : ℝ)^2153 ≤ (8942144619799/20000000000000 : ℝ)^1641 := by
    have hnat : (2707176009 : ℕ)^2153*20000000000000^1641 ≤ 8942144619799^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707176009 5000000000 8942144619799 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326274637/2500000000 : ℝ), (-978136029/5000000000 : ℝ), (2707176009/5000000000 : ℝ)] ![(8706156457221/20000000000000 : ℝ), (11758494599787/100000000000000 : ℝ), (8942144619799/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326274637/2500000000 : ℝ)|^2153 ≤ (8706156457221/20000000000000 : ℝ)^1641
        have hw : |(1326274637/2500000000 : ℝ)|=(1326274637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-978136029/5000000000 : ℝ)|^2153 ≤ (11758494599787/100000000000000 : ℝ)^1641
        have hw : |(-978136029/5000000000 : ℝ)|=(978136029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707176009/5000000000 : ℝ)|^2153 ≤ (8942144619799/20000000000000 : ℝ)^1641
        have hw : |(2707176009/5000000000 : ℝ)|=(2707176009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s4_6 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305098431/10000000000 : ℝ)*x 0 + (2707176037/5000000000 : ℝ)*x 1 + (-97813607/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305098431/10000000000 : ℝ)^2153 ≤ (43530781026529/100000000000000 : ℝ)^1641 := by
    have hnat : (5305098431 : ℕ)^2153*100000000000000^1641 ≤ 43530781026529^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305098431 10000000000 43530781026529 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707176037/5000000000 : ℝ)^2153 ≤ (8942144741143/20000000000000 : ℝ)^1641 := by
    have hnat : (2707176037 : ℕ)^2153*20000000000000^1641 ≤ 8942144741143^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707176037 5000000000 8942144741143 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97813607/500000000 : ℝ)^2153 ≤ (11758495246441/100000000000000 : ℝ)^1641 := by
    have hnat : (97813607 : ℕ)^2153*100000000000000^1641 ≤ 11758495246441^1641*500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97813607 500000000 11758495246441 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305098431/10000000000 : ℝ), (2707176037/5000000000 : ℝ), (-97813607/500000000 : ℝ)] ![(43530781026529/100000000000000 : ℝ), (8942144741143/20000000000000 : ℝ), (11758495246441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305098431/10000000000 : ℝ)|^2153 ≤ (43530781026529/100000000000000 : ℝ)^1641
        have hw : |(5305098431/10000000000 : ℝ)|=(5305098431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707176037/5000000000 : ℝ)|^2153 ≤ (8942144741143/20000000000000 : ℝ)^1641
        have hw : |(2707176037/5000000000 : ℝ)|=(2707176037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97813607/500000000 : ℝ)|^2153 ≤ (11758495246441/100000000000000 : ℝ)^1641
        have hw : |(-97813607/500000000 : ℝ)|=(97813607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s4_7 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2162714917/5000000000 : ℝ)*x 0 + (2254296003/5000000000 : ℝ)*x 1 + (4149283757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162714917/5000000000 : ℝ)^2153 ≤ (33301870656319/100000000000000 : ℝ)^1641 := by
    have hnat : (2162714917 : ℕ)^2153*100000000000000^1641 ≤ 33301870656319^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162714917 5000000000 33301870656319 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254296003/5000000000 : ℝ)^2153 ≤ (219775886071/625000000000 : ℝ)^1641 := by
    have hnat : (2254296003 : ℕ)^2153*625000000000^1641 ≤ 219775886071^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254296003 5000000000 219775886071 625000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4149283757/10000000000 : ℝ)^2153 ≤ (7883496889563/25000000000000 : ℝ)^1641 := by
    have hnat : (4149283757 : ℕ)^2153*25000000000000^1641 ≤ 7883496889563^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149283757 10000000000 7883496889563 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162714917/5000000000 : ℝ), (2254296003/5000000000 : ℝ), (4149283757/10000000000 : ℝ)] ![(33301870656319/100000000000000 : ℝ), (219775886071/625000000000 : ℝ), (7883496889563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162714917/5000000000 : ℝ)|^2153 ≤ (33301870656319/100000000000000 : ℝ)^1641
        have hw : |(2162714917/5000000000 : ℝ)|=(2162714917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254296003/5000000000 : ℝ)|^2153 ≤ (219775886071/625000000000 : ℝ)^1641
        have hw : |(2254296003/5000000000 : ℝ)|=(2254296003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4149283757/10000000000 : ℝ)|^2153 ≤ (7883496889563/25000000000000 : ℝ)^1641
        have hw : |(4149283757/10000000000 : ℝ)|=(4149283757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1346_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7503/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    (11109/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7503/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7503/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7503/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7503/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7503/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7503/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (68/625 : ℝ) ^ (4305/1024 : ℝ) ≤ (8910252959875487/100000000000000000000 : ℝ) := by
    have hpowers : (68/625 : ℝ)^4305 ≤ (8910252959875487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (68 : ℕ)^4305*100000000000000000000^1024 ≤ 8910252959875487^1024*625^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68 625 8910252959875487 100000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68/625 : ℝ)) (X := (8910252959875487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7503/50000 : ℝ) ^ (4305/1024 : ℝ) ≤ (17214886369283579/50000000000000000000 : ℝ) := by
    have hpowers : (7503/50000 : ℝ)^4305 ≤ (17214886369283579/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7503 : ℕ)^4305*50000000000000000000^1024 ≤ 17214886369283579^1024*50000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7503 50000 17214886369283579 50000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7503/50000 : ℝ)) (X := (17214886369283579/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008910252959875487/50000000000000000000 : ℝ) ≤ (1250052981878591/1250000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (50008910252959875487/50000000000000000000 : ℝ)^1024 ≤ (1250052981878591/1250000000000000 : ℝ)^4305 := by
      have hnat : (50008910252959875487 : ℕ)^1024*1250000000000000^4305 ≤ 1250052981878591^4305*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008910252959875487 50000000000000000000 1250052981878591 1250000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250052981878591/1250000000000000 : ℝ)) (X := (50008910252959875487/50000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008668005139688529/20000000000000000000 : ℝ) ≤ (5000515364210943/5000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (20008668005139688529/20000000000000000000 : ℝ)^1024 ≤ (5000515364210943/5000000000000000 : ℝ)^4305 := by
      have hnat : (20008668005139688529 : ℕ)^1024*5000000000000000^4305 ≤ 5000515364210943^4305*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008668005139688529 20000000000000000000 5000515364210943 5000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000515364210943/5000000000000000 : ℝ)) (X := (20008668005139688529/20000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017214886369283579/25000000000000000000 : ℝ) ≤ (2500409400453761/2500000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (25017214886369283579/25000000000000000000 : ℝ)^1024 ≤ (2500409400453761/2500000000000000 : ℝ)^4305 := by
      have hnat : (25017214886369283579 : ℕ)^1024*2500000000000000^4305 ≤ 2500409400453761^4305*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017214886369283579 25000000000000000000 2500409400453761 2500000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500409400453761/2500000000000000 : ℝ)) (X := (25017214886369283579/25000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8910252959875487/100000000000000000000 : ℝ) ≤ ((2578033953800838353/2578750000000000000 : ℝ)+2*(303436696579/206300000000000 : ℝ)*(68/625 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (2578033953800838353/2578750000000000000 : ℝ)+2*(303436696579/206300000000000 : ℝ)*(68/625 : ℝ)=(1250052981878591/1250000000000000 : ℝ) by norm_num, show 1+2*(8910252959875487/100000000000000000000 : ℝ)=(50008910252959875487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17214886369283579/50000000000000000000 : ℝ)+(8910252959875487/100000000000000000000 : ℝ) ≤ ((2578033953800838353/2578750000000000000 : ℝ)+(303436696579/206300000000000 : ℝ)*((7503/50000 : ℝ)+(68/625 : ℝ)))^(4305/1024 : ℝ) := by
    rw [show (2578033953800838353/2578750000000000000 : ℝ)+(303436696579/206300000000000 : ℝ)*((7503/50000 : ℝ)+(68/625 : ℝ))=(5000515364210943/5000000000000000 : ℝ) by norm_num, show 1+(17214886369283579/50000000000000000000 : ℝ)+(8910252959875487/100000000000000000000 : ℝ)=(20008668005139688529/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17214886369283579/50000000000000000000 : ℝ) ≤ ((2578033953800838353/2578750000000000000 : ℝ)+2*(303436696579/206300000000000 : ℝ)*(7503/50000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (2578033953800838353/2578750000000000000 : ℝ)+2*(303436696579/206300000000000 : ℝ)*(7503/50000 : ℝ)=(2500409400453761/2500000000000000 : ℝ) by norm_num, show 1+2*(17214886369283579/50000000000000000000 : ℝ)=(25017214886369283579/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2578033953800838353/2578750000000000000 : ℝ)*(X 1 0+X 2 0)+(303436696579/206300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (7503/50000 : ℝ)) (c := (2578033953800838353/2578750000000000000 : ℝ)) (alpha := (303436696579/206300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2578033953800838353/2578750000000000000 : ℝ)*(X 0 1+X 2 1)+(303436696579/206300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (7503/50000 : ℝ)) (c := (2578033953800838353/2578750000000000000 : ℝ)) (alpha := (303436696579/206300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2578033953800838353/2578750000000000000 : ℝ)*(X 0 2+X 1 2)+(303436696579/206300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (7503/50000 : ℝ)) (c := (2578033953800838353/2578750000000000000 : ℝ)) (alpha := (303436696579/206300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2040228519/10000000000 : ℝ)*X 0 0+(5414991043/10000000000 : ℝ)*X 0 1+(5242432091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674783151/5000000000 : ℝ)*X 1 0+(-2128192097/10000000000 : ℝ)*X 1 1+(1048486393/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349566653/10000000000 : ℝ)*X 2 0+(5242431817/10000000000 : ℝ)*X 2 1+(-133011989/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865080489/2000000000 : ℝ)*X 0 0+(1036985833/2500000000 : ℝ)*X 0 1+(2254962527/5000000000 : ℝ)*X 0 2+(865080489/2000000000 : ℝ)*X 1 0+(1036985833/2500000000 : ℝ)*X 1 1+(2254962527/5000000000 : ℝ)*X 1 2+(865080489/2000000000 : ℝ)*X 2 0+(1036985833/2500000000 : ℝ)*X 2 1+(2254962527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-510060493/2500000000 : ℝ)*X 0 0+(41944539/80000000 : ℝ)*X 0 1+(2707176101/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326274637/2500000000 : ℝ)*X 1 0+(-978136029/5000000000 : ℝ)*X 1 1+(2707176009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305098431/10000000000 : ℝ)*X 2 0+(2707176037/5000000000 : ℝ)*X 2 1+(-97813607/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162714917/5000000000 : ℝ)*X 0 0+(2254296003/5000000000 : ℝ)*X 0 1+(4149283757/10000000000 : ℝ)*X 0 2+(2162714917/5000000000 : ℝ)*X 1 0+(2254296003/5000000000 : ℝ)*X 1 1+(4149283757/10000000000 : ℝ)*X 1 2+(2162714917/5000000000 : ℝ)*X 2 0+(2254296003/5000000000 : ℝ)*X 2 1+(4149283757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (636080322162771800823/103150000000000000000000000 : ℝ) := by norm_num
    linear_combination (847471059/50000000000000 : ℝ)*(base19) + (1537720389/100000000000000 : ℝ)*(base23) + (28751769/10000000000000 : ℝ)*(lower2) + (116861831/100000000000000 : ℝ)*(upper3) + (2788083/2500000000000 : ℝ)*(upper5) + (427889377033487/10000000000000 : ℝ)*(major0) + (427889377033487/10000000000000 : ℝ)*(major1) + (427889377033487/10000000000000 : ℝ)*(major2) + (5795147561600211/100000000000000 : ℝ)*(sp0) + (2897590863142481/50000000000000 : ℝ)*(sp1) + (5795181883506691/100000000000000 : ℝ)*(sp2) + (552517060883663/20000000000000 : ℝ)*(sp3) + (3585962687/10000000000000 : ℝ)*(sp4) + (372189449/2000000000000 : ℝ)*(sp7) + (552520782778153/20000000000000 : ℝ)*(f.failure) + (144879585530677/2500000000000 : ℝ)*(f.sum) + (195088459147/32234375000000000000000000 : ℝ)*base65 + (14387989882773089/25787500000000000000000000000000 : ℝ)*base68 + (138032889118698089/25787500000000000000000000000000 : ℝ)*base70 + (47358440892876911/25787500000000000000000000000000 : ℝ)*base71 + (695795724557/128937500000000000000000000 : ℝ)*base74 + (286275373687464411/25787500000000000000000000000000 : ℝ)*base75 + (68979923532585589/25787500000000000000000000000000 : ℝ)*base78 + (2412276928326911/25787500000000000000000000000000 : ℝ)*base79 + (3618532059721/1031500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (202177/125000000000000000000 : ℝ)*base90 + (202177/125000000000000000000 : ℝ)*base92 + (202177/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (251773437930888461380124307/32234375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (724949467/50000000000000 : ℝ)*(base19) + (1430295097/100000000000000 : ℝ)*(base23) + (146621229/100000000000000 : ℝ)*(upper3) + (69049607/100000000000000 : ℝ)*(lower4) + (103105753/50000000000000 : ℝ)*(upper5) + (538834520130717/12500000000000 : ℝ)*(major0) + (538834520130717/12500000000000 : ℝ)*(major1) + (538834520130717/12500000000000 : ℝ)*(major2) + (23896455047/100000000000000 : ℝ)*(sp1) + (10695254141/50000000000000 : ℝ)*(sp2) + (233529132861303/4000000000000 : ℝ)*(sp4) + (2919101487589297/50000000000000 : ℝ)*(sp5) + (1459551375182299/25000000000000 : ℝ)*(sp6) + (13915618701009/500000000000 : ℝ)*(sp7) + (13915618701009/500000000000 : ℝ)*(f.failure) + (233529132861303/4000000000000 : ℝ)*(f.sum) + (9368739449411/2578750000000000000000000000 : ℝ)*base65 + (105256731154271113/16117187500000000000000000000000 : ℝ)*base67 + (192175606004245351/32234375000000000000000000000000 : ℝ)*base69 + (126447582881932851/32234375000000000000000000000000 : ℝ)*base71 + (58688193798609/10315000000000000000000000000 : ℝ)*base73 + (18192767376485747/4029296875000000000000000000000 : ℝ)*base75 + (210131117589620351/32234375000000000000000000000000 : ℝ)*base77 + (653687113508557851/32234375000000000000000000000000 : ℝ)*base79 + (137163023271/644687500000000000000000000 : ℝ)*base82 + (35481/3125000000000000000 : ℝ)*base90 + (35481/3125000000000000000 : ℝ)*base92 + (35481/3125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1346_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7503/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1346_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1346_s5_0 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-127529651/625000000 : ℝ)*x 0 + (1353219159/2500000000 : ℝ)*x 1 + (163887017/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127529651/625000000 : ℝ)^2153 ≤ (12426931623541/100000000000000 : ℝ)^1641 := by
    have hnat : (127529651 : ℕ)^2153*100000000000000^1641 ≤ 12426931623541^1641*625000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127529651 625000000 12426931623541 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353219159/2500000000 : ℝ)^2153 ≤ (44694739054807/100000000000000 : ℝ)^1641 := by
    have hnat : (1353219159 : ℕ)^2153*100000000000000^1641 ≤ 44694739054807^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353219159 2500000000 44694739054807 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163887017/312500000 : ℝ)^2153 ≤ (42878329298089/100000000000000 : ℝ)^1641 := by
    have hnat : (163887017 : ℕ)^2153*100000000000000^1641 ≤ 42878329298089^1641*312500000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163887017 312500000 42878329298089 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127529651/625000000 : ℝ), (1353219159/2500000000 : ℝ), (163887017/312500000 : ℝ)] ![(12426931623541/100000000000000 : ℝ), (44694739054807/100000000000000 : ℝ), (42878329298089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127529651/625000000 : ℝ)|^2153 ≤ (12426931623541/100000000000000 : ℝ)^1641
        have hw : |(-127529651/625000000 : ℝ)|=(127529651/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353219159/2500000000 : ℝ)|^2153 ≤ (44694739054807/100000000000000 : ℝ)^1641
        have hw : |(1353219159/2500000000 : ℝ)|=(1353219159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163887017/312500000 : ℝ)|^2153 ≤ (42878329298089/100000000000000 : ℝ)^1641
        have hw : |(163887017/312500000 : ℝ)|=(163887017/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s5_1 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349025407/10000000000 : ℝ)*x 0 + (-212632597/1000000000 : ℝ)*x 1 + (5244384559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349025407/10000000000 : ℝ)^2153 ≤ (440042912219/1000000000000 : ℝ)^1641 := by
    have hnat : (5349025407 : ℕ)^2153*1000000000000^1641 ≤ 440042912219^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349025407 10000000000 440042912219 1000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212632597/1000000000 : ℝ)^2153 ≤ (6558689651527/50000000000000 : ℝ)^1641 := by
    have hnat : (212632597 : ℕ)^2153*50000000000000^1641 ≤ 6558689651527^1641*1000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212632597 1000000000 6558689651527 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244384559/10000000000 : ℝ)^2153 ≤ (21439164729497/50000000000000 : ℝ)^1641 := by
    have hnat : (5244384559 : ℕ)^2153*50000000000000^1641 ≤ 21439164729497^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244384559 10000000000 21439164729497 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349025407/10000000000 : ℝ), (-212632597/1000000000 : ℝ), (5244384559/10000000000 : ℝ)] ![(440042912219/1000000000000 : ℝ), (6558689651527/50000000000000 : ℝ), (21439164729497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349025407/10000000000 : ℝ)|^2153 ≤ (440042912219/1000000000000 : ℝ)^1641
        have hw : |(5349025407/10000000000 : ℝ)|=(5349025407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212632597/1000000000 : ℝ)|^2153 ≤ (6558689651527/50000000000000 : ℝ)^1641
        have hw : |(-212632597/1000000000 : ℝ)|=(212632597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244384559/10000000000 : ℝ)|^2153 ≤ (21439164729497/50000000000000 : ℝ)^1641
        have hw : |(5244384559/10000000000 : ℝ)|=(5244384559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s5_2 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267451271/500000000 : ℝ)*x 0 + (81943509/156250000 : ℝ)*x 1 + (-2126325931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267451271/500000000 : ℝ)^2153 ≤ (44004291362213/100000000000000 : ℝ)^1641 := by
    have hnat : (267451271 : ℕ)^2153*100000000000000^1641 ≤ 44004291362213^1641*500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267451271 500000000 44004291362213 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81943509/156250000 : ℝ)^2153 ≤ (21439164820677/50000000000000 : ℝ)^1641 := by
    have hnat : (81943509 : ℕ)^2153*50000000000000^1641 ≤ 21439164820677^1641*156250000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81943509 156250000 21439164820677 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126325931/10000000000 : ℝ)^2153 ≤ (3279344746849/25000000000000 : ℝ)^1641 := by
    have hnat : (2126325931 : ℕ)^2153*25000000000000^1641 ≤ 3279344746849^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126325931 10000000000 3279344746849 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267451271/500000000 : ℝ), (81943509/156250000 : ℝ), (-2126325931/10000000000 : ℝ)] ![(44004291362213/100000000000000 : ℝ), (21439164820677/50000000000000 : ℝ), (3279344746849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267451271/500000000 : ℝ)|^2153 ≤ (44004291362213/100000000000000 : ℝ)^1641
        have hw : |(267451271/500000000 : ℝ)|=(267451271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81943509/156250000 : ℝ)|^2153 ≤ (21439164820677/50000000000000 : ℝ)^1641
        have hw : |(81943509/156250000 : ℝ)|=(81943509/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2126325931/10000000000 : ℝ)|^2153 ≤ (3279344746849/25000000000000 : ℝ)^1641
        have hw : |(-2126325931/10000000000 : ℝ)|=(2126325931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s5_3 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2162774189/5000000000 : ℝ)*x 0 + (2076095617/5000000000 : ℝ)*x 1 + (1126410317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162774189/5000000000 : ℝ)^2153 ≤ (8325767025789/25000000000000 : ℝ)^1641 := by
    have hnat : (2162774189 : ℕ)^2153*25000000000000^1641 ≤ 8325767025789^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162774189 5000000000 8325767025789 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076095617/5000000000 : ℝ)^2153 ≤ (15781490673049/50000000000000 : ℝ)^1641 := by
    have hnat : (2076095617 : ℕ)^2153*50000000000000^1641 ≤ 15781490673049^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076095617 5000000000 15781490673049 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126410317/2500000000 : ℝ)^2153 ≤ (35133950539451/100000000000000 : ℝ)^1641 := by
    have hnat : (1126410317 : ℕ)^2153*100000000000000^1641 ≤ 35133950539451^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126410317 2500000000 35133950539451 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162774189/5000000000 : ℝ), (2076095617/5000000000 : ℝ), (1126410317/2500000000 : ℝ)] ![(8325767025789/25000000000000 : ℝ), (15781490673049/50000000000000 : ℝ), (35133950539451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162774189/5000000000 : ℝ)|^2153 ≤ (8325767025789/25000000000000 : ℝ)^1641
        have hw : |(2162774189/5000000000 : ℝ)|=(2162774189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2076095617/5000000000 : ℝ)|^2153 ≤ (15781490673049/50000000000000 : ℝ)^1641
        have hw : |(2076095617/5000000000 : ℝ)|=(2076095617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126410317/2500000000 : ℝ)|^2153 ≤ (35133950539451/100000000000000 : ℝ)^1641
        have hw : |(1126410317/2500000000 : ℝ)|=(1126410317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s5_4 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1020243337/5000000000 : ℝ)*x 0 + (524499057/1000000000 : ℝ)*x 1 + (2706133749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020243337/5000000000 : ℝ)^2153 ≤ (3106757392471/25000000000000 : ℝ)^1641 := by
    have hnat : (1020243337 : ℕ)^2153*25000000000000^1641 ≤ 3106757392471^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020243337 5000000000 3106757392471 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524499057/1000000000 : ℝ)^2153 ≤ (1340150945737/3125000000000 : ℝ)^1641 := by
    have hnat : (524499057 : ℕ)^2153*3125000000000^1641 ≤ 1340150945737^1641*1000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524499057 1000000000 1340150945737 3125000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706133749/5000000000 : ℝ)^2153 ≤ (2793008759441/6250000000000 : ℝ)^1641 := by
    have hnat : (2706133749 : ℕ)^2153*6250000000000^1641 ≤ 2793008759441^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706133749 5000000000 2793008759441 6250000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1020243337/5000000000 : ℝ), (524499057/1000000000 : ℝ), (2706133749/5000000000 : ℝ)] ![(3106757392471/25000000000000 : ℝ), (1340150945737/3125000000000 : ℝ), (2793008759441/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1020243337/5000000000 : ℝ)|^2153 ≤ (3106757392471/25000000000000 : ℝ)^1641
        have hw : |(-1020243337/5000000000 : ℝ)|=(1020243337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524499057/1000000000 : ℝ)|^2153 ≤ (1340150945737/3125000000000 : ℝ)^1641
        have hw : |(524499057/1000000000 : ℝ)|=(524499057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706133749/5000000000 : ℝ)|^2153 ≤ (2793008759441/6250000000000 : ℝ)^1641
        have hw : |(2706133749/5000000000 : ℝ)|=(2706133749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s5_5 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652802849/5000000000 : ℝ)*x 0 + (-1958442979/10000000000 : ℝ)*x 1 + (1353066879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652802849/5000000000 : ℝ)^2153 ≤ (43536242144401/100000000000000 : ℝ)^1641 := by
    have hnat : (2652802849 : ℕ)^2153*100000000000000^1641 ≤ 43536242144401^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652802849 5000000000 43536242144401 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1958442979/10000000000 : ℝ)^2153 ≤ (11775617491099/100000000000000 : ℝ)^1641 := by
    have hnat : (1958442979 : ℕ)^2153*100000000000000^1641 ≤ 11775617491099^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958442979 10000000000 11775617491099 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353066879/2500000000 : ℝ)^2153 ≤ (893762806921/2000000000000 : ℝ)^1641 := by
    have hnat : (1353066879 : ℕ)^2153*2000000000000^1641 ≤ 893762806921^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353066879 2500000000 893762806921 2000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652802849/5000000000 : ℝ), (-1958442979/10000000000 : ℝ), (1353066879/2500000000 : ℝ)] ![(43536242144401/100000000000000 : ℝ), (11775617491099/100000000000000 : ℝ), (893762806921/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652802849/5000000000 : ℝ)|^2153 ≤ (43536242144401/100000000000000 : ℝ)^1641
        have hw : |(2652802849/5000000000 : ℝ)|=(2652802849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1958442979/10000000000 : ℝ)|^2153 ≤ (11775617491099/100000000000000 : ℝ)^1641
        have hw : |(-1958442979/10000000000 : ℝ)|=(1958442979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353066879/2500000000 : ℝ)|^2153 ≤ (893762806921/2000000000000 : ℝ)^1641
        have hw : |(1353066879/2500000000 : ℝ)|=(1353066879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s5_6 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652802837/5000000000 : ℝ)*x 0 + (5412267539/10000000000 : ℝ)*x 1 + (-1958442981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652802837/5000000000 : ℝ)^2153 ≤ (21768120943009/50000000000000 : ℝ)^1641 := by
    have hnat : (2652802837 : ℕ)^2153*50000000000000^1641 ≤ 21768120943009^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652802837 5000000000 21768120943009 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412267539/10000000000 : ℝ)^2153 ≤ (44688140595209/100000000000000 : ℝ)^1641 := by
    have hnat : (5412267539 : ℕ)^2153*100000000000000^1641 ≤ 44688140595209^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412267539 10000000000 44688140595209 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1958442981/10000000000 : ℝ)^2153 ≤ (2943904376719/25000000000000 : ℝ)^1641 := by
    have hnat : (1958442981 : ℕ)^2153*25000000000000^1641 ≤ 2943904376719^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958442981 10000000000 2943904376719 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652802837/5000000000 : ℝ), (5412267539/10000000000 : ℝ), (-1958442981/10000000000 : ℝ)] ![(21768120943009/50000000000000 : ℝ), (44688140595209/100000000000000 : ℝ), (2943904376719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652802837/5000000000 : ℝ)|^2153 ≤ (21768120943009/50000000000000 : ℝ)^1641
        have hw : |(2652802837/5000000000 : ℝ)|=(2652802837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412267539/10000000000 : ℝ)|^2153 ≤ (44688140595209/100000000000000 : ℝ)^1641
        have hw : |(5412267539/10000000000 : ℝ)|=(5412267539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1958442981/10000000000 : ℝ)|^2153 ≤ (2943904376719/25000000000000 : ℝ)^1641
        have hw : |(-1958442981/10000000000 : ℝ)|=(1958442981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s5_7 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2162787043/5000000000 : ℝ)*x 0 + (1126092533/2500000000 : ℝ)*x 1 + (4153469029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162787043/5000000000 : ℝ)^2153 ≤ (16651663894183/50000000000000 : ℝ)^1641 := by
    have hnat : (2162787043 : ℕ)^2153*50000000000000^1641 ≤ 16651663894183^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162787043 5000000000 16651663894183 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126092533/2500000000 : ℝ)^2153 ≤ (7024189297317/20000000000000 : ℝ)^1641 := by
    have hnat : (1126092533 : ℕ)^2153*20000000000000^1641 ≤ 7024189297317^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126092533 2500000000 7024189297317 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4153469029/10000000000 : ℝ)^2153 ≤ (15787862854831/50000000000000 : ℝ)^1641 := by
    have hnat : (4153469029 : ℕ)^2153*50000000000000^1641 ≤ 15787862854831^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153469029 10000000000 15787862854831 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162787043/5000000000 : ℝ), (1126092533/2500000000 : ℝ), (4153469029/10000000000 : ℝ)] ![(16651663894183/50000000000000 : ℝ), (7024189297317/20000000000000 : ℝ), (15787862854831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162787043/5000000000 : ℝ)|^2153 ≤ (16651663894183/50000000000000 : ℝ)^1641
        have hw : |(2162787043/5000000000 : ℝ)|=(2162787043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126092533/2500000000 : ℝ)|^2153 ≤ (7024189297317/20000000000000 : ℝ)^1641
        have hw : |(1126092533/2500000000 : ℝ)|=(1126092533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4153469029/10000000000 : ℝ)|^2153 ≤ (15787862854831/50000000000000 : ℝ)^1641
        have hw : |(4153469029/10000000000 : ℝ)|=(4153469029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1346_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11151/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7359/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11109/100000 : ℝ) ^ (4305/1024 : ℝ) ≤ (4862847396861377/50000000000000000000 : ℝ) := by
    have hpowers : (11109/100000 : ℝ)^4305 ≤ (4862847396861377/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11109 : ℕ)^4305*50000000000000000000^1024 ≤ 4862847396861377^1024*100000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11109 100000 4862847396861377 50000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11109/100000 : ℝ)) (X := (4862847396861377/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (4305/1024 : ℝ) ≤ (16068378217820721/50000000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^4305 ≤ (16068378217820721/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7381 : ℕ)^4305*50000000000000000000^1024 ≤ 16068378217820721^1024*50000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 16068378217820721 50000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (16068378217820721/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004862847396861377/25000000000000000000 : ℝ) ≤ (2500115660549973/2500000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (25004862847396861377/25000000000000000000 : ℝ)^1024 ≤ (2500115660549973/2500000000000000 : ℝ)^4305 := by
      have hnat : (25004862847396861377 : ℕ)^1024*2500000000000000^4305 ≤ 2500115660549973^4305*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004862847396861377 25000000000000000000 2500115660549973 2500000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500115660549973/2500000000000000 : ℝ)) (X := (25004862847396861377/25000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010465612807341049/25000000000000000000 : ℝ) ≤ (10000995593806593/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (25010465612807341049/25000000000000000000 : ℝ)^1024 ≤ (10000995593806593/10000000000000000 : ℝ)^4305 := by
      have hnat : (25010465612807341049 : ℕ)^1024*10000000000000000^4305 ≤ 10000995593806593^4305*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010465612807341049 25000000000000000000 10000995593806593 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000995593806593/10000000000000000 : ℝ)) (X := (25010465612807341049/25000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016068378217820721/25000000000000000000 : ℝ) ≤ (5000764272706647/5000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (25016068378217820721/25000000000000000000 : ℝ)^1024 ≤ (5000764272706647/5000000000000000 : ℝ)^4305 := by
      have hnat : (25016068378217820721 : ℕ)^1024*5000000000000000^4305 ≤ 5000764272706647^4305*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016068378217820721 25000000000000000000 5000764272706647 5000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000764272706647/5000000000000000 : ℝ)) (X := (25016068378217820721/25000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4862847396861377/50000000000000000000 : ℝ) ≤ ((18259924456579261329/18265000000000000000 : ℝ)+2*(532951606701/365300000000000 : ℝ)*(11109/100000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (18259924456579261329/18265000000000000000 : ℝ)+2*(532951606701/365300000000000 : ℝ)*(11109/100000 : ℝ)=(2500115660549973/2500000000000000 : ℝ) by norm_num, show 1+2*(4862847396861377/50000000000000000000 : ℝ)=(25004862847396861377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16068378217820721/50000000000000000000 : ℝ)+(4862847396861377/50000000000000000000 : ℝ) ≤ ((18259924456579261329/18265000000000000000 : ℝ)+(532951606701/365300000000000 : ℝ)*((7381/50000 : ℝ)+(11109/100000 : ℝ)))^(4305/1024 : ℝ) := by
    rw [show (18259924456579261329/18265000000000000000 : ℝ)+(532951606701/365300000000000 : ℝ)*((7381/50000 : ℝ)+(11109/100000 : ℝ))=(10000995593806593/10000000000000000 : ℝ) by norm_num, show 1+(16068378217820721/50000000000000000000 : ℝ)+(4862847396861377/50000000000000000000 : ℝ)=(25010465612807341049/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16068378217820721/50000000000000000000 : ℝ) ≤ ((18259924456579261329/18265000000000000000 : ℝ)+2*(532951606701/365300000000000 : ℝ)*(7381/50000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (18259924456579261329/18265000000000000000 : ℝ)+2*(532951606701/365300000000000 : ℝ)*(7381/50000 : ℝ)=(5000764272706647/5000000000000000 : ℝ) by norm_num, show 1+2*(16068378217820721/50000000000000000000 : ℝ)=(25016068378217820721/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18259924456579261329/18265000000000000000 : ℝ)*(X 1 0+X 2 0)+(532951606701/365300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (18259924456579261329/18265000000000000000 : ℝ)) (alpha := (532951606701/365300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18259924456579261329/18265000000000000000 : ℝ)*(X 0 1+X 2 1)+(532951606701/365300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (18259924456579261329/18265000000000000000 : ℝ)) (alpha := (532951606701/365300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18259924456579261329/18265000000000000000 : ℝ)*(X 0 2+X 1 2)+(532951606701/365300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (18259924456579261329/18265000000000000000 : ℝ)) (alpha := (532951606701/365300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-127529651/625000000 : ℝ)*X 0 0+(1353219159/2500000000 : ℝ)*X 0 1+(163887017/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349025407/10000000000 : ℝ)*X 1 0+(-212632597/1000000000 : ℝ)*X 1 1+(5244384559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267451271/500000000 : ℝ)*X 2 0+(81943509/156250000 : ℝ)*X 2 1+(-2126325931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162774189/5000000000 : ℝ)*X 0 0+(2076095617/5000000000 : ℝ)*X 0 1+(1126410317/2500000000 : ℝ)*X 0 2+(2162774189/5000000000 : ℝ)*X 1 0+(2076095617/5000000000 : ℝ)*X 1 1+(1126410317/2500000000 : ℝ)*X 1 2+(2162774189/5000000000 : ℝ)*X 2 0+(2076095617/5000000000 : ℝ)*X 2 1+(1126410317/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1020243337/5000000000 : ℝ)*X 0 0+(524499057/1000000000 : ℝ)*X 0 1+(2706133749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652802849/5000000000 : ℝ)*X 1 0+(-1958442979/10000000000 : ℝ)*X 1 1+(1353066879/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652802837/5000000000 : ℝ)*X 2 0+(5412267539/10000000000 : ℝ)*X 2 1+(-1958442981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162787043/5000000000 : ℝ)*X 0 0+(1126092533/2500000000 : ℝ)*X 0 1+(4153469029/10000000000 : ℝ)*X 0 2+(2162787043/5000000000 : ℝ)*X 1 0+(1126092533/2500000000 : ℝ)*X 1 1+(4153469029/10000000000 : ℝ)*X 1 2+(2162787043/5000000000 : ℝ)*X 2 0+(1126092533/2500000000 : ℝ)*X 2 1+(4153469029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1846347093501193225221659301/456625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80287819/10000000000000 : ℝ)*(base19) + (809243543/100000000000000 : ℝ)*(base23) + (2155347/50000000000000 : ℝ)*(lower2) + (17701369/20000000000000 : ℝ)*(upper3) + (16650013/12500000000000 : ℝ)*(upper5) + (2191075196499941/50000000000000 : ℝ)*(major0) + (2191075196499941/50000000000000 : ℝ)*(major1) + (2191075196499941/50000000000000 : ℝ)*(major2) + (1187002527645811/20000000000000 : ℝ)*(sp0) + (148375745920069/2500000000000 : ℝ)*(sp1) + (5935029830437407/100000000000000 : ℝ)*(sp2) + (1414631186763201/50000000000000 : ℝ)*(sp3) + (3600290379/20000000000000 : ℝ)*(sp4) + (3819005123/50000000000000 : ℝ)*(sp7) + (353658751442081/12500000000000 : ℝ)*(f.failure) + (118700612793619/2000000000000 : ℝ)*(f.sum) + (28772966531/2283125000000000000000000000 : ℝ)*base66 + (4860668666923368411/913250000000000000000000000000000 : ℝ)*base68 + (3420420293170868411/913250000000000000000000000000000 : ℝ)*base70 + (5472238184319868411/913250000000000000000000000000000 : ℝ)*base72 + (24065956812091/9132500000000000000000000000 : ℝ)*base73 + (9612116670953368411/913250000000000000000000000000000 : ℝ)*base76 + (17229567197034868411/913250000000000000000000000000000 : ℝ)*base78 + (18371969813974868411/913250000000000000000000000000000 : ℝ)*base80 + (117186899347737/18265000000000000000000000000 : ℝ)*base81 + (121171/78125000000000000000 : ℝ)*base89 + (121171/78125000000000000000 : ℝ)*base91 + (121171/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4503828945102386898105961167/456625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109645359/6250000000000 : ℝ)*(base19) + (182437463/10000000000000 : ℝ)*(base23) + (5485359/2500000000000 : ℝ)*(upper3) + (42043769/100000000000000 : ℝ)*(lower4) + (49139237/25000000000000 : ℝ)*(upper5) + (2206978729479047/50000000000000 : ℝ)*(major0) + (2206978729479047/50000000000000 : ℝ)*(major1) + (2206978729479047/50000000000000 : ℝ)*(major2) + (17755940391/50000000000000 : ℝ)*(sp1) + (18846312203/50000000000000 : ℝ)*(sp2) + (373631801255413/6250000000000 : ℝ)*(sp4) + (2989035776940041/50000000000000 : ℝ)*(sp5) + (1494517325771893/25000000000000 : ℝ)*(sp6) + (712451442263233/25000000000000 : ℝ)*(sp7) + (712451442263233/25000000000000 : ℝ)*(f.failure) + (373631801255413/6250000000000 : ℝ)*(f.sum) + (2894555678753/9132500000000000000000000000 : ℝ)*base66 + (1956691069647776537/913250000000000000000000000000000 : ℝ)*base68 + (11045808249868776537/913250000000000000000000000000000 : ℝ)*base70 + (1612708222381276537/913250000000000000000000000000000 : ℝ)*base72 + (14242665901913/2283125000000000000000000000 : ℝ)*base73 + (18090796528593276537/913250000000000000000000000000000 : ℝ)*base76 + (3062536924709776537/913250000000000000000000000000000 : ℝ)*base78 + (17166139771250776537/913250000000000000000000000000000 : ℝ)*base80 + (11790213612093/2283125000000000000000000000 : ℝ)*base81 + (1510897/156250000000000000000 : ℝ)*base90 + (1510897/156250000000000000000 : ℝ)*base92 + (1510897/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1346_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1346_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1346_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2011/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4939/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1346_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1346_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1346_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2011/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4939/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1346_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

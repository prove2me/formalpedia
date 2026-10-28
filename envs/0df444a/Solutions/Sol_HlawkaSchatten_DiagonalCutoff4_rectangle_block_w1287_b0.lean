-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1287_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:29.669813+00:00
-- url     : https://prove2.me/submissions/32e65b00-ffb5-4bad-9f85-4af7a2eb32b5

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
theorem support_rectangle_w1287_s0_0 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-921056051/5000000000 : ℝ)*x 0 + (3010506131/5000000000 : ℝ)*x 1 + (38380943/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (921056051/5000000000 : ℝ)^4247 ≤ (5381023793437/50000000000000 : ℝ)^3223 := by
    have hnat : (921056051 : ℕ)^4247*50000000000000^3223 ≤ 5381023793437^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921056051 5000000000 5381023793437 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3010506131/5000000000 : ℝ)^4247 ≤ (12811704342879/25000000000000 : ℝ)^3223 := by
    have hnat : (3010506131 : ℕ)^4247*25000000000000^3223 ≤ 12811704342879^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3010506131 5000000000 12811704342879 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38380943/80000000 : ℝ)^4247 ≤ (9497783756627/25000000000000 : ℝ)^3223 := by
    have hnat : (38380943 : ℕ)^4247*25000000000000^3223 ≤ 9497783756627^3223*80000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38380943 80000000 9497783756627 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-921056051/5000000000 : ℝ), (3010506131/5000000000 : ℝ), (38380943/80000000 : ℝ)] ![(5381023793437/50000000000000 : ℝ), (12811704342879/25000000000000 : ℝ), (9497783756627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-921056051/5000000000 : ℝ)|^4247 ≤ (5381023793437/50000000000000 : ℝ)^3223
        have hw : |(-921056051/5000000000 : ℝ)|=(921056051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3010506131/5000000000 : ℝ)|^4247 ≤ (12811704342879/25000000000000 : ℝ)^3223
        have hw : |(3010506131/5000000000 : ℝ)|=(3010506131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(38380943/80000000 : ℝ)|^4247 ≤ (9497783756627/25000000000000 : ℝ)^3223
        have hw : |(38380943/80000000 : ℝ)|=(38380943/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s0_1 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5507979993/10000000000 : ℝ)*x 0 + (-508062357/2000000000 : ℝ)*x 1 + (959523587/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5507979993/10000000000 : ℝ)^4247 ≤ (45572344716687/100000000000000 : ℝ)^3223 := by
    have hnat : (5507979993 : ℕ)^4247*100000000000000^3223 ≤ 45572344716687^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507979993 10000000000 45572344716687 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508062357/2000000000 : ℝ)^4247 ≤ (4109129904647/25000000000000 : ℝ)^3223 := by
    have hnat : (508062357 : ℕ)^4247*25000000000000^3223 ≤ 4109129904647^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508062357 2000000000 4109129904647 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959523587/2000000000 : ℝ)^4247 ≤ (9497783913147/25000000000000 : ℝ)^3223 := by
    have hnat : (959523587 : ℕ)^4247*25000000000000^3223 ≤ 9497783913147^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959523587 2000000000 9497783913147 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5507979993/10000000000 : ℝ), (-508062357/2000000000 : ℝ), (959523587/2000000000 : ℝ)] ![(45572344716687/100000000000000 : ℝ), (4109129904647/25000000000000 : ℝ), (9497783913147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5507979993/10000000000 : ℝ)|^4247 ≤ (45572344716687/100000000000000 : ℝ)^3223
        have hw : |(5507979993/10000000000 : ℝ)|=(5507979993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-508062357/2000000000 : ℝ)|^4247 ≤ (4109129904647/25000000000000 : ℝ)^3223
        have hw : |(-508062357/2000000000 : ℝ)|=(508062357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(959523587/2000000000 : ℝ)|^4247 ≤ (9497783913147/25000000000000 : ℝ)^3223
        have hw : |(959523587/2000000000 : ℝ)|=(959523587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s0_2 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2753989821/5000000000 : ℝ)*x 0 + (4797618459/10000000000 : ℝ)*x 1 + (-2540311591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753989821/5000000000 : ℝ)^4247 ≤ (45572340889867/100000000000000 : ℝ)^3223 := by
    have hnat : (2753989821 : ℕ)^4247*100000000000000^3223 ≤ 45572340889867^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753989821 5000000000 45572340889867 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4797618459/10000000000 : ℝ)^4247 ≤ (37991141120353/100000000000000 : ℝ)^3223 := by
    have hnat : (4797618459 : ℕ)^4247*100000000000000^3223 ≤ 37991141120353^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4797618459 10000000000 37991141120353 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540311591/10000000000 : ℝ)^4247 ≤ (16436517964547/100000000000000 : ℝ)^3223 := by
    have hnat : (2540311591 : ℕ)^4247*100000000000000^3223 ≤ 16436517964547^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540311591 10000000000 16436517964547 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753989821/5000000000 : ℝ), (4797618459/10000000000 : ℝ), (-2540311591/10000000000 : ℝ)] ![(45572340889867/100000000000000 : ℝ), (37991141120353/100000000000000 : ℝ), (16436517964547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753989821/5000000000 : ℝ)|^4247 ≤ (45572340889867/100000000000000 : ℝ)^3223
        have hw : |(2753989821/5000000000 : ℝ)|=(2753989821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4797618459/10000000000 : ℝ)|^4247 ≤ (37991141120353/100000000000000 : ℝ)^3223
        have hw : |(4797618459/10000000000 : ℝ)|=(4797618459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2540311591/10000000000 : ℝ)|^4247 ≤ (16436517964547/100000000000000 : ℝ)^3223
        have hw : |(-2540311591/10000000000 : ℝ)|=(2540311591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s0_3 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4187102071/10000000000 : ℝ)*x 0 + (3109764411/10000000000 : ℝ)*x 1 + (5619325153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187102071/10000000000 : ℝ)^4247 ≤ (15876664990103/50000000000000 : ℝ)^3223 := by
    have hnat : (4187102071 : ℕ)^4247*50000000000000^3223 ≤ 15876664990103^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187102071 10000000000 15876664990103 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3109764411/10000000000 : ℝ)^4247 ≤ (21456490383909/100000000000000 : ℝ)^3223 := by
    have hnat : (3109764411 : ℕ)^4247*100000000000000^3223 ≤ 21456490383909^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3109764411 10000000000 21456490383909 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5619325153/10000000000 : ℝ)^4247 ≤ (46790179632457/100000000000000 : ℝ)^3223 := by
    have hnat : (5619325153 : ℕ)^4247*100000000000000^3223 ≤ 46790179632457^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5619325153 10000000000 46790179632457 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187102071/10000000000 : ℝ), (3109764411/10000000000 : ℝ), (5619325153/10000000000 : ℝ)] ![(15876664990103/50000000000000 : ℝ), (21456490383909/100000000000000 : ℝ), (46790179632457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187102071/10000000000 : ℝ)|^4247 ≤ (15876664990103/50000000000000 : ℝ)^3223
        have hw : |(4187102071/10000000000 : ℝ)|=(4187102071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3109764411/10000000000 : ℝ)|^4247 ≤ (21456490383909/100000000000000 : ℝ)^3223
        have hw : |(3109764411/10000000000 : ℝ)|=(3109764411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5619325153/10000000000 : ℝ)|^4247 ≤ (46790179632457/100000000000000 : ℝ)^3223
        have hw : |(5619325153/10000000000 : ℝ)|=(5619325153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s0_4 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46171589/250000000 : ℝ)*x 0 + (4829200839/10000000000 : ℝ)*x 1 + (748538309/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46171589/250000000 : ℝ)^4247 ≤ (2699660304683/25000000000000 : ℝ)^3223 := by
    have hnat : (46171589 : ℕ)^4247*25000000000000^3223 ≤ 2699660304683^3223*250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46171589 250000000 2699660304683 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4829200839/10000000000 : ℝ)^4247 ≤ (38321036848261/100000000000000 : ℝ)^3223 := by
    have hnat : (4829200839 : ℕ)^4247*100000000000000^3223 ≤ 38321036848261^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829200839 10000000000 38321036848261 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748538309/1250000000 : ℝ)^4247 ≤ (1272008047681/2500000000000 : ℝ)^3223 := by
    have hnat : (748538309 : ℕ)^4247*2500000000000^3223 ≤ 1272008047681^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748538309 1250000000 1272008047681 2500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46171589/250000000 : ℝ), (4829200839/10000000000 : ℝ), (748538309/1250000000 : ℝ)] ![(2699660304683/25000000000000 : ℝ), (38321036848261/100000000000000 : ℝ), (1272008047681/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46171589/250000000 : ℝ)|^4247 ≤ (2699660304683/25000000000000 : ℝ)^3223
        have hw : |(-46171589/250000000 : ℝ)|=(46171589/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4829200839/10000000000 : ℝ)|^4247 ≤ (38321036848261/100000000000000 : ℝ)^3223
        have hw : |(4829200839/10000000000 : ℝ)|=(4829200839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(748538309/1250000000 : ℝ)|^4247 ≤ (1272008047681/2500000000000 : ℝ)^3223
        have hw : |(748538309/1250000000 : ℝ)|=(748538309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s0_5 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (323434847/625000000 : ℝ)*x 0 + (-1349621029/10000000000 : ℝ)*x 1 + (5988309057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323434847/625000000 : ℝ)^4247 ≤ (2623555773469/6250000000000 : ℝ)^3223 := by
    have hnat : (323434847 : ℕ)^4247*6250000000000^3223 ≤ 2623555773469^3223*625000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323434847 625000000 2623555773469 6250000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349621029/10000000000 : ℝ)^4247 ≤ (3571378380607/50000000000000 : ℝ)^3223 := by
    have hnat : (1349621029 : ℕ)^4247*50000000000000^3223 ≤ 3571378380607^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349621029 10000000000 3571378380607 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5988309057/10000000000 : ℝ)^4247 ≤ (12720087712307/25000000000000 : ℝ)^3223 := by
    have hnat : (5988309057 : ℕ)^4247*25000000000000^3223 ≤ 12720087712307^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5988309057 10000000000 12720087712307 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323434847/625000000 : ℝ), (-1349621029/10000000000 : ℝ), (5988309057/10000000000 : ℝ)] ![(2623555773469/6250000000000 : ℝ), (3571378380607/50000000000000 : ℝ), (12720087712307/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323434847/625000000 : ℝ)|^4247 ≤ (2623555773469/6250000000000 : ℝ)^3223
        have hw : |(323434847/625000000 : ℝ)|=(323434847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1349621029/10000000000 : ℝ)|^4247 ≤ (3571378380607/50000000000000 : ℝ)^3223
        have hw : |(-1349621029/10000000000 : ℝ)|=(1349621029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5988309057/10000000000 : ℝ)|^4247 ≤ (12720087712307/25000000000000 : ℝ)^3223
        have hw : |(5988309057/10000000000 : ℝ)|=(5988309057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s0_6 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174958813/10000000000 : ℝ)*x 0 + (5988306883/10000000000 : ℝ)*x 1 + (-1349622587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174958813/10000000000 : ℝ)^4247 ≤ (41976905853973/100000000000000 : ℝ)^3223 := by
    have hnat : (5174958813 : ℕ)^4247*100000000000000^3223 ≤ 41976905853973^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174958813 10000000000 41976905853973 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5988306883/10000000000 : ℝ)^4247 ≤ (3180020406803/6250000000000 : ℝ)^3223 := by
    have hnat : (5988306883 : ℕ)^4247*6250000000000^3223 ≤ 3180020406803^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5988306883 10000000000 3180020406803 6250000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349622587/10000000000 : ℝ)^4247 ≤ (7142767626559/100000000000000 : ℝ)^3223 := by
    have hnat : (1349622587 : ℕ)^4247*100000000000000^3223 ≤ 7142767626559^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349622587 10000000000 7142767626559 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174958813/10000000000 : ℝ), (5988306883/10000000000 : ℝ), (-1349622587/10000000000 : ℝ)] ![(41976905853973/100000000000000 : ℝ), (3180020406803/6250000000000 : ℝ), (7142767626559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174958813/10000000000 : ℝ)|^4247 ≤ (41976905853973/100000000000000 : ℝ)^3223
        have hw : |(5174958813/10000000000 : ℝ)|=(5174958813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5988306883/10000000000 : ℝ)|^4247 ≤ (3180020406803/6250000000000 : ℝ)^3223
        have hw : |(5988306883/10000000000 : ℝ)|=(5988306883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1349622587/10000000000 : ℝ)|^4247 ≤ (7142767626559/100000000000000 : ℝ)^3223
        have hw : |(-1349622587/10000000000 : ℝ)|=(1349622587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s0_7 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (419685229/1000000000 : ℝ)*x 0 + (1388636733/2500000000 : ℝ)*x 1 + (317684659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419685229/1000000000 : ℝ)^4247 ≤ (31850800345813/100000000000000 : ℝ)^3223 := by
    have hnat : (419685229 : ℕ)^4247*100000000000000^3223 ≤ 31850800345813^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419685229 1000000000 31850800345813 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1388636733/2500000000 : ℝ)^4247 ≤ (46080727040593/100000000000000 : ℝ)^3223 := by
    have hnat : (1388636733 : ℕ)^4247*100000000000000^3223 ≤ 46080727040593^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388636733 2500000000 46080727040593 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317684659/1000000000 : ℝ)^4247 ≤ (2206847259857/10000000000000 : ℝ)^3223 := by
    have hnat : (317684659 : ℕ)^4247*10000000000000^3223 ≤ 2206847259857^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317684659 1000000000 2206847259857 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419685229/1000000000 : ℝ), (1388636733/2500000000 : ℝ), (317684659/1000000000 : ℝ)] ![(31850800345813/100000000000000 : ℝ), (46080727040593/100000000000000 : ℝ), (2206847259857/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419685229/1000000000 : ℝ)|^4247 ≤ (31850800345813/100000000000000 : ℝ)^3223
        have hw : |(419685229/1000000000 : ℝ)|=(419685229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1388636733/2500000000 : ℝ)|^4247 ≤ (46080727040593/100000000000000 : ℝ)^3223
        have hw : |(1388636733/2500000000 : ℝ)|=(1388636733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317684659/1000000000 : ℝ)|^4247 ≤ (2206847259857/10000000000000 : ℝ)^3223
        have hw : |(317684659/1000000000 : ℝ)|=(317684659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1287_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (993/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3409/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2123/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2123 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2123*1^512 ≤ 0^512*1^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2123/512 : ℝ) ≤ (2238452957556575527/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2123 ≤ (2238452957556575527/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2123*100000000000000000000^512 ≤ 2238452957556575527^512*5^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2238452957556575527 100000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2238452957556575527/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2123 := by
      have hnat : (1 : ℕ)^512*1^2123 ≤ 1^2123*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102238452957556575527/100000000000000000000 : ℝ) ≤ (2513382947926677/2500000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (102238452957556575527/100000000000000000000 : ℝ)^512 ≤ (2513382947926677/2500000000000000 : ℝ)^2123 := by
      have hnat : (102238452957556575527 : ℕ)^512*2500000000000000^2123 ≤ 2513382947926677^2123*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102238452957556575527 100000000000000000000 2513382947926677 2500000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513382947926677/2500000000000000 : ℝ)) (X := (102238452957556575527/100000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52238452957556575527/50000000000000000000 : ℝ) ≤ (1263382947926677/1250000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (52238452957556575527/50000000000000000000 : ℝ)^512 ≤ (1263382947926677/1250000000000000 : ℝ)^2123 := by
      have hnat : (52238452957556575527 : ℕ)^512*1250000000000000^2123 ≤ 1263382947926677^2123*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52238452957556575527 50000000000000000000 1263382947926677 1250000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1263382947926677/1250000000000000 : ℝ)) (X := (52238452957556575527/50000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(13382947926677/1000000000000000 : ℝ)*(0 : ℝ))^(2123/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(13382947926677/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2238452957556575527/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(13382947926677/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2123/512 : ℝ) := by
    rw [show (1 : ℝ)+(13382947926677/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2513382947926677/2500000000000000 : ℝ) by norm_num, show 1+(2238452957556575527/100000000000000000000 : ℝ)+(0 : ℝ)=(102238452957556575527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2238452957556575527/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(13382947926677/1000000000000000 : ℝ)*(2/5 : ℝ))^(2123/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(13382947926677/1000000000000000 : ℝ)*(2/5 : ℝ)=(1263382947926677/1250000000000000 : ℝ) by norm_num, show 1+2*(2238452957556575527/100000000000000000000 : ℝ)=(52238452957556575527/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(13382947926677/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13382947926677/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(13382947926677/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13382947926677/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(13382947926677/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13382947926677/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-921056051/5000000000 : ℝ)*X 0 0+(3010506131/5000000000 : ℝ)*X 0 1+(38380943/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5507979993/10000000000 : ℝ)*X 1 0+(-508062357/2000000000 : ℝ)*X 1 1+(959523587/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2753989821/5000000000 : ℝ)*X 2 0+(4797618459/10000000000 : ℝ)*X 2 1+(-2540311591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4187102071/10000000000 : ℝ)*X 0 0+(3109764411/10000000000 : ℝ)*X 0 1+(5619325153/10000000000 : ℝ)*X 0 2+(4187102071/10000000000 : ℝ)*X 1 0+(3109764411/10000000000 : ℝ)*X 1 1+(5619325153/10000000000 : ℝ)*X 1 2+(4187102071/10000000000 : ℝ)*X 2 0+(3109764411/10000000000 : ℝ)*X 2 1+(5619325153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-46171589/250000000 : ℝ)*X 0 0+(4829200839/10000000000 : ℝ)*X 0 1+(748538309/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((323434847/625000000 : ℝ)*X 1 0+(-1349621029/10000000000 : ℝ)*X 1 1+(5988309057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174958813/10000000000 : ℝ)*X 2 0+(5988306883/10000000000 : ℝ)*X 2 1+(-1349622587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((419685229/1000000000 : ℝ)*X 0 0+(1388636733/2500000000 : ℝ)*X 0 1+(317684659/1000000000 : ℝ)*X 0 2+(419685229/1000000000 : ℝ)*X 1 0+(1388636733/2500000000 : ℝ)*X 1 1+(317684659/1000000000 : ℝ)*X 1 2+(419685229/1000000000 : ℝ)*X 2 0+(1388636733/2500000000 : ℝ)*X 2 1+(317684659/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4420571754623418315339/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159926991/100000000000000 : ℝ)*(base1) + (1805829951/100000000000000 : ℝ)*(base19) + (1753740103/100000000000000 : ℝ)*(base23) + (11840047/6250000000000 : ℝ)*(upper3) + (220037827/100000000000000 : ℝ)*(upper5) + (949914161631/156250000000 : ℝ)*(major0) + (949914161631/156250000000 : ℝ)*(major1) + (949914161631/156250000000 : ℝ)*(major2) + (817403172745703/100000000000000 : ℝ)*(sp0) + (102175862855067/12500000000000 : ℝ)*(sp1) + (51087934683149/6250000000000 : ℝ)*(sp2) + (398478556759607/100000000000000 : ℝ)*(sp3) + (227834071/4000000000000 : ℝ)*(sp4) + (616441691/25000000000000 : ℝ)*(sp7) + (199240591226681/50000000000000 : ℝ)*(f.failure) + (817408708670487/100000000000000 : ℝ)*(f.sum) + (2518406502879/625000000000000000000000000 : ℝ)*base66 + (843379634813/156250000000000000000000000 : ℝ)*base68 + (58276395203/39062500000000000000000000 : ℝ)*base69 + (3886248519877/625000000000000000000000000 : ℝ)*base72 + (2901955761629/625000000000000000000000000 : ℝ)*base74 + (712067823627/625000000000000000000000000 : ℝ)*base76 + (3537402444877/625000000000000000000000000 : ℝ)*base78 + (2572211567377/625000000000000000000000000 : ℝ)*base80 + (281324912121/625000000000000000000000000 : ℝ)*base81 + (9653271/1250000000000000000000 : ℝ)*base89 + (9653271/1250000000000000000000 : ℝ)*base91 + (9653271/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41075930086988756513259/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (368832841/100000000000000 : ℝ)*(base1) + (480811637/100000000000000 : ℝ)*(base19) + (79610541/12500000000000 : ℝ)*(base23) + (15793617/25000000000000 : ℝ)*(upper3) + (320827539945637/50000000000000 : ℝ)*(major0) + (320827539945637/50000000000000 : ℝ)*(major1) + (320827539945637/50000000000000 : ℝ)*(major2) + (69214259/6250000000000 : ℝ)*(sp1) + (53187007/20000000000000 : ℝ)*(sp2) + (77274531/10000000000000 : ℝ)*(sp3) + (34509352289963/4000000000000 : ℝ)*(sp4) + (862731850176453/100000000000000 : ℝ)*(sp5) + (107841566949609/12500000000000 : ℝ)*(sp6) + (26285966890771/6250000000000 : ℝ)*(sp7) + (420576611830487/100000000000000 : ℝ)*(f.failure) + (172546687683247/20000000000000 : ℝ)*(f.sum) + (79716955808249/25000000000000000000000000000 : ℝ)*base65 + (381497967708249/50000000000000000000000000000 : ℝ)*base67 + (657814938558249/50000000000000000000000000000 : ℝ)*base69 + (350184817158249/50000000000000000000000000000 : ℝ)*base71 + (84424232433249/25000000000000000000000000000 : ℝ)*base73 + (678430735508249/50000000000000000000000000000 : ℝ)*base75 + (398977599258249/50000000000000000000000000000 : ℝ)*base77 + (49012611908249/50000000000000000000000000000 : ℝ)*base79 + (205944489033249/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (19612583/2500000000000000000000 : ℝ)*base90 + (19612583/2500000000000000000000 : ℝ)*base92 + (19612583/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1287_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (993/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3409/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1287_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1287_s1_0 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-406976657/2000000000 : ℝ)*x 0 + (5667711619/10000000000 : ℝ)*x 1 + (3927739/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406976657/2000000000 : ℝ)^4247 ≤ (12270186274199/100000000000000 : ℝ)^3223 := by
    have hnat : (406976657 : ℕ)^4247*100000000000000^3223 ≤ 12270186274199^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406976657 2000000000 12270186274199 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5667711619/10000000000 : ℝ)^4247 ≤ (47321808934661/100000000000000 : ℝ)^3223 := by
    have hnat : (5667711619 : ℕ)^4247*100000000000000^3223 ≤ 47321808934661^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5667711619 10000000000 47321808934661 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3927739/7812500 : ℝ)^4247 ≤ (40408004784787/100000000000000 : ℝ)^3223 := by
    have hnat : (3927739 : ℕ)^4247*100000000000000^3223 ≤ 40408004784787^3223*7812500^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3927739 7812500 40408004784787 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-406976657/2000000000 : ℝ), (5667711619/10000000000 : ℝ), (3927739/7812500 : ℝ)] ![(12270186274199/100000000000000 : ℝ), (47321808934661/100000000000000 : ℝ), (40408004784787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-406976657/2000000000 : ℝ)|^4247 ≤ (12270186274199/100000000000000 : ℝ)^3223
        have hw : |(-406976657/2000000000 : ℝ)|=(406976657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5667711619/10000000000 : ℝ)|^4247 ≤ (47321808934661/100000000000000 : ℝ)^3223
        have hw : |(5667711619/10000000000 : ℝ)|=(5667711619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3927739/7812500 : ℝ)|^4247 ≤ (40408004784787/100000000000000 : ℝ)^3223
        have hw : |(3927739/7812500 : ℝ)|=(3927739/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s1_1 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5411516633/10000000000 : ℝ)*x 0 + (-475636177/2000000000 : ℝ)*x 1 + (5027505807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411516633/10000000000 : ℝ)^4247 ≤ (22261789424747/50000000000000 : ℝ)^3223 := by
    have hnat : (5411516633 : ℕ)^4247*50000000000000^3223 ≤ 22261789424747^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411516633 10000000000 22261789424747 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475636177/2000000000 : ℝ)^4247 ≤ (7534208770963/50000000000000 : ℝ)^3223 := by
    have hnat : (475636177 : ℕ)^4247*50000000000000^3223 ≤ 7534208770963^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475636177 2000000000 7534208770963 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5027505807/10000000000 : ℝ)^4247 ≤ (8081600717601/20000000000000 : ℝ)^3223 := by
    have hnat : (5027505807 : ℕ)^4247*20000000000000^3223 ≤ 8081600717601^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027505807 10000000000 8081600717601 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411516633/10000000000 : ℝ), (-475636177/2000000000 : ℝ), (5027505807/10000000000 : ℝ)] ![(22261789424747/50000000000000 : ℝ), (7534208770963/50000000000000 : ℝ), (8081600717601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411516633/10000000000 : ℝ)|^4247 ≤ (22261789424747/50000000000000 : ℝ)^3223
        have hw : |(5411516633/10000000000 : ℝ)|=(5411516633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-475636177/2000000000 : ℝ)|^4247 ≤ (7534208770963/50000000000000 : ℝ)^3223
        have hw : |(-475636177/2000000000 : ℝ)|=(475636177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5027505807/10000000000 : ℝ)|^4247 ≤ (8081600717601/20000000000000 : ℝ)^3223
        have hw : |(5027505807/10000000000 : ℝ)|=(5027505807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s1_2 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2705758217/5000000000 : ℝ)*x 0 + (5027505933/10000000000 : ℝ)*x 1 + (-297272623/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705758217/5000000000 : ℝ)^4247 ≤ (22261788346009/50000000000000 : ℝ)^3223 := by
    have hnat : (2705758217 : ℕ)^4247*50000000000000^3223 ≤ 22261788346009^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705758217 5000000000 22261788346009 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5027505933/10000000000 : ℝ)^4247 ≤ (4040800492247/10000000000000 : ℝ)^3223 := by
    have hnat : (5027505933 : ℕ)^4247*10000000000000^3223 ≤ 4040800492247^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027505933 10000000000 4040800492247 10000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297272623/1250000000 : ℝ)^4247 ≤ (15068418368497/100000000000000 : ℝ)^3223 := by
    have hnat : (297272623 : ℕ)^4247*100000000000000^3223 ≤ 15068418368497^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297272623 1250000000 15068418368497 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705758217/5000000000 : ℝ), (5027505933/10000000000 : ℝ), (-297272623/1250000000 : ℝ)] ![(22261788346009/50000000000000 : ℝ), (4040800492247/10000000000000 : ℝ), (15068418368497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705758217/5000000000 : ℝ)|^4247 ≤ (22261788346009/50000000000000 : ℝ)^3223
        have hw : |(2705758217/5000000000 : ℝ)|=(2705758217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5027505933/10000000000 : ℝ)|^4247 ≤ (4040800492247/10000000000000 : ℝ)^3223
        have hw : |(5027505933/10000000000 : ℝ)|=(5027505933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-297272623/1250000000 : ℝ)|^4247 ≤ (15068418368497/100000000000000 : ℝ)^3223
        have hw : |(-297272623/1250000000 : ℝ)|=(297272623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s1_3 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151007673/5000000000 : ℝ)*x 0 + (147718587/400000000 : ℝ)*x 1 + (125155639/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151007673/5000000000 : ℝ)^4247 ≤ (6581327738823/20000000000000 : ℝ)^3223 := by
    have hnat : (2151007673 : ℕ)^4247*20000000000000^3223 ≤ 6581327738823^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151007673 5000000000 6581327738823 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147718587/400000000 : ℝ)^4247 ≤ (26910585002539/100000000000000 : ℝ)^3223 := by
    have hnat : (147718587 : ℕ)^4247*100000000000000^3223 ≤ 26910585002539^3223*400000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147718587 400000000 26910585002539 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125155639/250000000 : ℝ)^4247 ≤ (40182776288589/100000000000000 : ℝ)^3223 := by
    have hnat : (125155639 : ℕ)^4247*100000000000000^3223 ≤ 40182776288589^3223*250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125155639 250000000 40182776288589 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151007673/5000000000 : ℝ), (147718587/400000000 : ℝ), (125155639/250000000 : ℝ)] ![(6581327738823/20000000000000 : ℝ), (26910585002539/100000000000000 : ℝ), (40182776288589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151007673/5000000000 : ℝ)|^4247 ≤ (6581327738823/20000000000000 : ℝ)^3223
        have hw : |(2151007673/5000000000 : ℝ)|=(2151007673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(147718587/400000000 : ℝ)|^4247 ≤ (26910585002539/100000000000000 : ℝ)^3223
        have hw : |(147718587/400000000 : ℝ)|=(147718587/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125155639/250000000 : ℝ)|^4247 ≤ (40182776288589/100000000000000 : ℝ)^3223
        have hw : |(125155639/250000000 : ℝ)|=(125155639/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s1_4 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1017765641/5000000000 : ℝ)*x 0 + (5035884463/10000000000 : ℝ)*x 1 + (5659173961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017765641/5000000000 : ℝ)^4247 ≤ (6137667670759/50000000000000 : ℝ)^3223 := by
    have hnat : (1017765641 : ℕ)^4247*50000000000000^3223 ≤ 6137667670759^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017765641 5000000000 6137667670759 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5035884463/10000000000 : ℝ)^4247 ≤ (20248382688641/50000000000000 : ℝ)^3223 := by
    have hnat : (5035884463 : ℕ)^4247*50000000000000^3223 ≤ 20248382688641^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5035884463 10000000000 20248382688641 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5659173961/10000000000 : ℝ)^4247 ≤ (47227899261677/100000000000000 : ℝ)^3223 := by
    have hnat : (5659173961 : ℕ)^4247*100000000000000^3223 ≤ 47227899261677^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5659173961 10000000000 47227899261677 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1017765641/5000000000 : ℝ), (5035884463/10000000000 : ℝ), (5659173961/10000000000 : ℝ)] ![(6137667670759/50000000000000 : ℝ), (20248382688641/50000000000000 : ℝ), (47227899261677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1017765641/5000000000 : ℝ)|^4247 ≤ (6137667670759/50000000000000 : ℝ)^3223
        have hw : |(-1017765641/5000000000 : ℝ)|=(1017765641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5035884463/10000000000 : ℝ)|^4247 ≤ (20248382688641/50000000000000 : ℝ)^3223
        have hw : |(5035884463/10000000000 : ℝ)|=(5035884463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5659173961/10000000000 : ℝ)|^4247 ≤ (47227899261677/100000000000000 : ℝ)^3223
        have hw : |(5659173961/10000000000 : ℝ)|=(5659173961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s1_5 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1311545991/2500000000 : ℝ)*x 0 + (-436628133/2500000000 : ℝ)*x 1 + (5659174527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311545991/2500000000 : ℝ)^4247 ≤ (42739870527927/100000000000000 : ℝ)^3223 := by
    have hnat : (1311545991 : ℕ)^4247*100000000000000^3223 ≤ 42739870527927^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311545991 2500000000 42739870527927 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436628133/2500000000 : ℝ)^4247 ≤ (10032223961211/100000000000000 : ℝ)^3223 := by
    have hnat : (436628133 : ℕ)^4247*100000000000000^3223 ≤ 10032223961211^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436628133 2500000000 10032223961211 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5659174527/10000000000 : ℝ)^4247 ≤ (47227905485883/100000000000000 : ℝ)^3223 := by
    have hnat : (5659174527 : ℕ)^4247*100000000000000^3223 ≤ 47227905485883^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5659174527 10000000000 47227905485883 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311545991/2500000000 : ℝ), (-436628133/2500000000 : ℝ), (5659174527/10000000000 : ℝ)] ![(42739870527927/100000000000000 : ℝ), (10032223961211/100000000000000 : ℝ), (47227905485883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311545991/2500000000 : ℝ)|^4247 ≤ (42739870527927/100000000000000 : ℝ)^3223
        have hw : |(1311545991/2500000000 : ℝ)|=(1311545991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436628133/2500000000 : ℝ)|^4247 ≤ (10032223961211/100000000000000 : ℝ)^3223
        have hw : |(-436628133/2500000000 : ℝ)|=(436628133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5659174527/10000000000 : ℝ)|^4247 ≤ (47227905485883/100000000000000 : ℝ)^3223
        have hw : |(5659174527/10000000000 : ℝ)|=(5659174527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s1_6 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5246183871/10000000000 : ℝ)*x 0 + (2829587083/5000000000 : ℝ)*x 1 + (-174651319/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246183871/10000000000 : ℝ)^4247 ≤ (854797390591/2000000000000 : ℝ)^3223 := by
    have hnat : (5246183871 : ℕ)^4247*2000000000000^3223 ≤ 854797390591^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246183871 10000000000 854797390591 2000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829587083/5000000000 : ℝ)^4247 ≤ (47227901516027/100000000000000 : ℝ)^3223 := by
    have hnat : (2829587083 : ℕ)^4247*100000000000000^3223 ≤ 47227901516027^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829587083 5000000000 47227901516027 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174651319/1000000000 : ℝ)^4247 ≤ (2508057235429/25000000000000 : ℝ)^3223 := by
    have hnat : (174651319 : ℕ)^4247*25000000000000^3223 ≤ 2508057235429^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174651319 1000000000 2508057235429 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246183871/10000000000 : ℝ), (2829587083/5000000000 : ℝ), (-174651319/1000000000 : ℝ)] ![(854797390591/2000000000000 : ℝ), (47227901516027/100000000000000 : ℝ), (2508057235429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246183871/10000000000 : ℝ)|^4247 ≤ (854797390591/2000000000000 : ℝ)^3223
        have hw : |(5246183871/10000000000 : ℝ)|=(5246183871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2829587083/5000000000 : ℝ)|^4247 ≤ (47227901516027/100000000000000 : ℝ)^3223
        have hw : |(2829587083/5000000000 : ℝ)|=(2829587083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-174651319/1000000000 : ℝ)|^4247 ≤ (2508057235429/25000000000000 : ℝ)^3223
        have hw : |(-174651319/1000000000 : ℝ)|=(174651319/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s1_7 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4303343979/10000000000 : ℝ)*x 0 + (31181493/62500000 : ℝ)*x 1 + (3710477433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303343979/10000000000 : ℝ)^4247 ≤ (16460015569431/50000000000000 : ℝ)^3223 := by
    have hnat : (4303343979 : ℕ)^4247*50000000000000^3223 ≤ 16460015569431^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303343979 10000000000 16460015569431 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31181493/62500000 : ℝ)^4247 ≤ (20000548301099/50000000000000 : ℝ)^3223 := by
    have hnat : (31181493 : ℕ)^4247*50000000000000^3223 ≤ 20000548301099^3223*62500000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31181493 62500000 20000548301099 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3710477433/10000000000 : ℝ)^4247 ≤ (676971806009/2500000000000 : ℝ)^3223 := by
    have hnat : (3710477433 : ℕ)^4247*2500000000000^3223 ≤ 676971806009^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3710477433 10000000000 676971806009 2500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303343979/10000000000 : ℝ), (31181493/62500000 : ℝ), (3710477433/10000000000 : ℝ)] ![(16460015569431/50000000000000 : ℝ), (20000548301099/50000000000000 : ℝ), (676971806009/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303343979/10000000000 : ℝ)|^4247 ≤ (16460015569431/50000000000000 : ℝ)^3223
        have hw : |(4303343979/10000000000 : ℝ)|=(4303343979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31181493/62500000 : ℝ)|^4247 ≤ (20000548301099/50000000000000 : ℝ)^3223
        have hw : |(31181493/62500000 : ℝ)|=(31181493/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3710477433/10000000000 : ℝ)|^4247 ≤ (676971806009/2500000000000 : ℝ)^3223
        have hw : |(3710477433/10000000000 : ℝ)|=(3710477433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1287_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3409/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6359/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19891/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3409/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3409/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3409/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3409/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3409/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3409/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (993/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (123686233689/25000000000000000000 : ℝ) := by
    have hpowers : (993/100000 : ℝ)^2123 ≤ (123686233689/25000000000000000000 : ℝ)^512 := by
      have hnat : (993 : ℕ)^2123*25000000000000000000^512 ≤ 123686233689^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        993 100000 123686233689 25000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (993/100000 : ℝ)) (X := (123686233689/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3409/12500 : ℝ) ^ (2123/512 : ℝ) ≤ (114327134183654683/25000000000000000000 : ℝ) := by
    have hpowers : (3409/12500 : ℝ)^2123 ≤ (114327134183654683/25000000000000000000 : ℝ)^512 := by
      have hnat : (3409 : ℕ)^2123*25000000000000000000^512 ≤ 114327134183654683^512*12500^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3409 12500 114327134183654683 25000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3409/12500 : ℝ)) (X := (114327134183654683/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000123686233689/12500000000000000000 : ℝ) ≤ (2000000004772669/2000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (12500000123686233689/12500000000000000000 : ℝ)^512 ≤ (2000000004772669/2000000000000000 : ℝ)^2123 := by
      have hnat : (12500000123686233689 : ℕ)^512*2000000000000000^2123 ≤ 2000000004772669^2123*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000123686233689 12500000000000000000 2000000004772669 2000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000004772669/2000000000000000 : ℝ)) (X := (12500000123686233689/12500000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6278581814467472093/6250000000000000000 : ℝ) ≤ (10011009752660393/10000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (6278581814467472093/6250000000000000000 : ℝ)^512 ≤ (10011009752660393/10000000000000000 : ℝ)^2123 := by
      have hnat : (6278581814467472093 : ℕ)^512*10000000000000000^2123 ≤ 10011009752660393^2123*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6278581814467472093 6250000000000000000 10011009752660393 10000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011009752660393/10000000000000000 : ℝ)) (X := (6278581814467472093/6250000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12614327134183654683/12500000000000000000 : ℝ) ≤ (10022019481457441/10000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (12614327134183654683/12500000000000000000 : ℝ)^512 ≤ (10022019481457441/10000000000000000 : ℝ)^2123 := by
      have hnat : (12614327134183654683 : ℕ)^512*10000000000000000^2123 ≤ 10022019481457441^2123*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12614327134183654683 12500000000000000000 10022019481457441 10000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022019481457441/10000000000000000 : ℝ)) (X := (12614327134183654683/12500000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(123686233689/25000000000000000000 : ℝ) ≤ ((262768135305713905927/262790000000000000000 : ℝ)+2*(1376216099631/328487500000000 : ℝ)*(993/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (262768135305713905927/262790000000000000000 : ℝ)+2*(1376216099631/328487500000000 : ℝ)*(993/100000 : ℝ)=(2000000004772669/2000000000000000 : ℝ) by norm_num, show 1+2*(123686233689/25000000000000000000 : ℝ)=(12500000123686233689/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(114327134183654683/25000000000000000000 : ℝ)+(123686233689/25000000000000000000 : ℝ) ≤ ((262768135305713905927/262790000000000000000 : ℝ)+(1376216099631/328487500000000 : ℝ)*((3409/12500 : ℝ)+(993/100000 : ℝ)))^(2123/512 : ℝ) := by
    rw [show (262768135305713905927/262790000000000000000 : ℝ)+(1376216099631/328487500000000 : ℝ)*((3409/12500 : ℝ)+(993/100000 : ℝ))=(10011009752660393/10000000000000000 : ℝ) by norm_num, show 1+(114327134183654683/25000000000000000000 : ℝ)+(123686233689/25000000000000000000 : ℝ)=(6278581814467472093/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(114327134183654683/25000000000000000000 : ℝ) ≤ ((262768135305713905927/262790000000000000000 : ℝ)+2*(1376216099631/328487500000000 : ℝ)*(3409/12500 : ℝ))^(2123/512 : ℝ) := by
    rw [show (262768135305713905927/262790000000000000000 : ℝ)+2*(1376216099631/328487500000000 : ℝ)*(3409/12500 : ℝ)=(10022019481457441/10000000000000000 : ℝ) by norm_num, show 1+2*(114327134183654683/25000000000000000000 : ℝ)=(12614327134183654683/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (262768135305713905927/262790000000000000000 : ℝ)*(X 1 0+X 2 0)+(1376216099631/328487500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (993/100000 : ℝ)) (hi := (3409/12500 : ℝ)) (c := (262768135305713905927/262790000000000000000 : ℝ)) (alpha := (1376216099631/328487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (262768135305713905927/262790000000000000000 : ℝ)*(X 0 1+X 2 1)+(1376216099631/328487500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (993/100000 : ℝ)) (hi := (3409/12500 : ℝ)) (c := (262768135305713905927/262790000000000000000 : ℝ)) (alpha := (1376216099631/328487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (262768135305713905927/262790000000000000000 : ℝ)*(X 0 2+X 1 2)+(1376216099631/328487500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (993/100000 : ℝ)) (hi := (3409/12500 : ℝ)) (c := (262768135305713905927/262790000000000000000 : ℝ)) (alpha := (1376216099631/328487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-406976657/2000000000 : ℝ)*X 0 0+(5667711619/10000000000 : ℝ)*X 0 1+(3927739/7812500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5411516633/10000000000 : ℝ)*X 1 0+(-475636177/2000000000 : ℝ)*X 1 1+(5027505807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2705758217/5000000000 : ℝ)*X 2 0+(5027505933/10000000000 : ℝ)*X 2 1+(-297272623/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2151007673/5000000000 : ℝ)*X 0 0+(147718587/400000000 : ℝ)*X 0 1+(125155639/250000000 : ℝ)*X 0 2+(2151007673/5000000000 : ℝ)*X 1 0+(147718587/400000000 : ℝ)*X 1 1+(125155639/250000000 : ℝ)*X 1 2+(2151007673/5000000000 : ℝ)*X 2 0+(147718587/400000000 : ℝ)*X 2 1+(125155639/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1017765641/5000000000 : ℝ)*X 0 0+(5035884463/10000000000 : ℝ)*X 0 1+(5659173961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1311545991/2500000000 : ℝ)*X 1 0+(-436628133/2500000000 : ℝ)*X 1 1+(5659174527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5246183871/10000000000 : ℝ)*X 2 0+(2829587083/5000000000 : ℝ)*X 2 1+(-174651319/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4303343979/10000000000 : ℝ)*X 0 0+(31181493/62500000 : ℝ)*X 0 1+(3710477433/10000000000 : ℝ)*X 0 2+(4303343979/10000000000 : ℝ)*X 1 0+(31181493/62500000 : ℝ)*X 1 1+(3710477433/10000000000 : ℝ)*X 1 2+(4303343979/10000000000 : ℝ)*X 2 0+(31181493/62500000 : ℝ)*X 2 1+(3710477433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1893427418863812335027003007/597250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7833657/25000000000000 : ℝ)*(base1) + (124459211/20000000000000 : ℝ)*(base19) + (564855821/100000000000000 : ℝ)*(base23) + (86982169/100000000000000 : ℝ)*(upper3) + (34725763/100000000000000 : ℝ)*(upper5) + (580867757408939/50000000000000 : ℝ)*(major0) + (580867757408939/50000000000000 : ℝ)*(major1) + (580867757408939/50000000000000 : ℝ)*(major2) + (1562001557845761/100000000000000 : ℝ)*(sp0) + (78100194854251/5000000000000 : ℝ)*(sp1) + (781001977262627/50000000000000 : ℝ)*(sp2) + (76146473943413/10000000000000 : ℝ)*(sp3) + (1496434971/50000000000000 : ℝ)*(sp4) + (1633811163/100000000000000 : ℝ)*(sp7) + (761466404579921/100000000000000 : ℝ)*(f.failure) + (62480180775243/4000000000000 : ℝ)*(f.sum) + (3637761902839/2986250000000000000000000000 : ℝ)*base66 + (12185658766607310777/1194500000000000000000000000000000 : ℝ)*base68 + (6320006034294310777/1194500000000000000000000000000000 : ℝ)*base70 + (11810168673486310777/1194500000000000000000000000000000 : ℝ)*base72 + (33619423749973/5972500000000000000000000000 : ℝ)*base74 + (4077124152225310777/1194500000000000000000000000000000 : ℝ)*base76 + (5531741188518310777/1194500000000000000000000000000000 : ℝ)*base78 + (7116468068233810777/1194500000000000000000000000000000 : ℝ)*base80 + (34345243463531/11945000000000000000000000000 : ℝ)*base82 + (7610111/2500000000000000000000 : ℝ)*base89 + (7610111/2500000000000000000000 : ℝ)*base91 + (7610111/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1236177525806803044269459709/119450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32733747/100000000000000 : ℝ)*(base1) + (401277297/20000000000000 : ℝ)*(base19) + (968065271/50000000000000 : ℝ)*(base23) + (6996023/2500000000000 : ℝ)*(upper3) + (226723281/100000000000000 : ℝ)*(upper5) + (238651962904179/20000000000000 : ℝ)*(major0) + (238651962904179/20000000000000 : ℝ)*(major1) + (238651962904179/20000000000000 : ℝ)*(major2) + (2100405791/20000000000000 : ℝ)*(sp1) + (1146901243/12500000000000 : ℝ)*(sp2) + (1604390123804071/100000000000000 : ℝ)*(sp4) + (401094395663721/25000000000000 : ℝ)*(sp5) + (802189489864919/50000000000000 : ℝ)*(sp6) + (156425832054797/20000000000000 : ℝ)*(sp7) + (195532298251933/25000000000000 : ℝ)*(f.failure) + (401097522767581/25000000000000 : ℝ)*(f.sum) + (613981915621/477800000000000000000000000 : ℝ)*base66 + (1201439699884269903/477800000000000000000000000000000 : ℝ)*base67 + (4134004812217130097/477800000000000000000000000000000 : ℝ)*base70 + (403342063423130097/477800000000000000000000000000000 : ℝ)*base72 + (3135833164779/2389000000000000000000000000 : ℝ)*base73 + (3293356956868730097/477800000000000000000000000000000 : ℝ)*base76 + (1450714974276530097/477800000000000000000000000000000 : ℝ)*base78 + (3215589083104330097/477800000000000000000000000000000 : ℝ)*base80 + (11973175282449/2389000000000000000000000000 : ℝ)*base82 + (691197/625000000000000000000 : ℝ)*base90 + (691197/625000000000000000000 : ℝ)*base92 + (691197/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1287_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3409/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19891/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1287_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1287_s2_0 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-520011857/2500000000 : ℝ)*x 0 + (1099160623/2000000000 : ℝ)*x 1 + (517057561/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520011857/2500000000 : ℝ)^4247 ≤ (12630307163381/100000000000000 : ℝ)^3223 := by
    have hnat : (520011857 : ℕ)^4247*100000000000000^3223 ≤ 12630307163381^3223*2500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520011857 2500000000 12630307163381 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099160623/2000000000 : ℝ)^4247 ≤ (45439631461181/100000000000000 : ℝ)^3223 := by
    have hnat : (1099160623 : ℕ)^4247*100000000000000^3223 ≤ 45439631461181^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099160623 2000000000 45439631461181 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517057561/1000000000 : ℝ)^4247 ≤ (20965030676607/50000000000000 : ℝ)^3223 := by
    have hnat : (517057561 : ℕ)^4247*50000000000000^3223 ≤ 20965030676607^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517057561 1000000000 20965030676607 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-520011857/2500000000 : ℝ), (1099160623/2000000000 : ℝ), (517057561/1000000000 : ℝ)] ![(12630307163381/100000000000000 : ℝ), (45439631461181/100000000000000 : ℝ), (20965030676607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-520011857/2500000000 : ℝ)|^4247 ≤ (12630307163381/100000000000000 : ℝ)^3223
        have hw : |(-520011857/2500000000 : ℝ)|=(520011857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099160623/2000000000 : ℝ)|^4247 ≤ (45439631461181/100000000000000 : ℝ)^3223
        have hw : |(1099160623/2000000000 : ℝ)|=(1099160623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517057561/1000000000 : ℝ)|^4247 ≤ (20965030676607/50000000000000 : ℝ)^3223
        have hw : |(517057561/1000000000 : ℝ)|=(517057561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s2_1 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671245197/1250000000 : ℝ)*x 0 + (-2248639379/10000000000 : ℝ)*x 1 + (2585288019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671245197/1250000000 : ℝ)^4247 ≤ (2754600403529/6250000000000 : ℝ)^3223 := by
    have hnat : (671245197 : ℕ)^4247*6250000000000^3223 ≤ 2754600403529^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671245197 1250000000 2754600403529 6250000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248639379/10000000000 : ℝ)^4247 ≤ (2799265519727/20000000000000 : ℝ)^3223 := by
    have hnat : (2248639379 : ℕ)^4247*20000000000000^3223 ≤ 2799265519727^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248639379 10000000000 2799265519727 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585288019/5000000000 : ℝ)^4247 ≤ (41930065926753/100000000000000 : ℝ)^3223 := by
    have hnat : (2585288019 : ℕ)^4247*100000000000000^3223 ≤ 41930065926753^3223*5000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585288019 5000000000 41930065926753 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671245197/1250000000 : ℝ), (-2248639379/10000000000 : ℝ), (2585288019/5000000000 : ℝ)] ![(2754600403529/6250000000000 : ℝ), (2799265519727/20000000000000 : ℝ), (41930065926753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671245197/1250000000 : ℝ)|^4247 ≤ (2754600403529/6250000000000 : ℝ)^3223
        have hw : |(671245197/1250000000 : ℝ)|=(671245197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2248639379/10000000000 : ℝ)|^4247 ≤ (2799265519727/20000000000000 : ℝ)^3223
        have hw : |(-2248639379/10000000000 : ℝ)|=(2248639379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585288019/5000000000 : ℝ)|^4247 ≤ (41930065926753/100000000000000 : ℝ)^3223
        have hw : |(2585288019/5000000000 : ℝ)|=(2585288019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s2_2 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335622613/625000000 : ℝ)*x 0 + (103411513/200000000 : ℝ)*x 1 + (-2248639579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335622613/625000000 : ℝ)^4247 ≤ (1101840224139/2500000000000 : ℝ)^3223 := by
    have hnat : (335622613 : ℕ)^4247*2500000000000^3223 ≤ 1101840224139^3223*625000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335622613 625000000 1101840224139 2500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103411513/200000000 : ℝ)^4247 ≤ (5241257722581/12500000000000 : ℝ)^3223 := by
    have hnat : (103411513 : ℕ)^4247*12500000000000^3223 ≤ 5241257722581^3223*200000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103411513 200000000 5241257722581 12500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248639579/10000000000 : ℝ)^4247 ≤ (6998164619511/50000000000000 : ℝ)^3223 := by
    have hnat : (2248639579 : ℕ)^4247*50000000000000^3223 ≤ 6998164619511^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248639579 10000000000 6998164619511 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335622613/625000000 : ℝ), (103411513/200000000 : ℝ), (-2248639579/10000000000 : ℝ)] ![(1101840224139/2500000000000 : ℝ), (5241257722581/12500000000000 : ℝ), (6998164619511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335622613/625000000 : ℝ)|^4247 ≤ (1101840224139/2500000000000 : ℝ)^3223
        have hw : |(335622613/625000000 : ℝ)|=(335622613/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103411513/200000000 : ℝ)|^4247 ≤ (5241257722581/12500000000000 : ℝ)^3223
        have hw : |(103411513/200000000 : ℝ)|=(103411513/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2248639579/10000000000 : ℝ)|^4247 ≤ (6998164619511/50000000000000 : ℝ)^3223
        have hw : |(-2248639579/10000000000 : ℝ)|=(2248639579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s2_3 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541674231/1250000000 : ℝ)*x 0 + (4012080093/10000000000 : ℝ)*x 1 + (4679229833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541674231/1250000000 : ℝ)^4247 ≤ (16611640092921/50000000000000 : ℝ)^3223 := by
    have hnat : (541674231 : ℕ)^4247*50000000000000^3223 ≤ 16611640092921^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541674231 1250000000 16611640092921 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4012080093/10000000000 : ℝ)^4247 ≤ (15008027218099/50000000000000 : ℝ)^3223 := by
    have hnat : (4012080093 : ℕ)^4247*50000000000000^3223 ≤ 15008027218099^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012080093 10000000000 15008027218099 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4679229833/10000000000 : ℝ)^4247 ≤ (36760665358053/100000000000000 : ℝ)^3223 := by
    have hnat : (4679229833 : ℕ)^4247*100000000000000^3223 ≤ 36760665358053^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4679229833 10000000000 36760665358053 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541674231/1250000000 : ℝ), (4012080093/10000000000 : ℝ), (4679229833/10000000000 : ℝ)] ![(16611640092921/50000000000000 : ℝ), (15008027218099/50000000000000 : ℝ), (36760665358053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541674231/1250000000 : ℝ)|^4247 ≤ (16611640092921/50000000000000 : ℝ)^3223
        have hw : |(541674231/1250000000 : ℝ)|=(541674231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4012080093/10000000000 : ℝ)|^4247 ≤ (15008027218099/50000000000000 : ℝ)^3223
        have hw : |(4012080093/10000000000 : ℝ)|=(4012080093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4679229833/10000000000 : ℝ)|^4247 ≤ (36760665358053/100000000000000 : ℝ)^3223
        have hw : |(4679229833/10000000000 : ℝ)|=(4679229833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s2_4 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104006577/500000000 : ℝ)*x 0 + (1034549479/2000000000 : ℝ)*x 1 + (5493610963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104006577/500000000 : ℝ)^4247 ≤ (12630980176267/100000000000000 : ℝ)^3223 := by
    have hnat : (104006577 : ℕ)^4247*100000000000000^3223 ≤ 12630980176267^3223*500000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104006577 500000000 12630980176267 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034549479/2000000000 : ℝ)^4247 ≤ (10488317560719/25000000000000 : ℝ)^3223 := by
    have hnat : (1034549479 : ℕ)^4247*25000000000000^3223 ≤ 10488317560719^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034549479 2000000000 10488317560719 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5493610963/10000000000 : ℝ)^4247 ≤ (22707874784547/50000000000000 : ℝ)^3223 := by
    have hnat : (5493610963 : ℕ)^4247*50000000000000^3223 ≤ 22707874784547^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493610963 10000000000 22707874784547 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104006577/500000000 : ℝ), (1034549479/2000000000 : ℝ), (5493610963/10000000000 : ℝ)] ![(12630980176267/100000000000000 : ℝ), (10488317560719/25000000000000 : ℝ), (22707874784547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104006577/500000000 : ℝ)|^4247 ≤ (12630980176267/100000000000000 : ℝ)^3223
        have hw : |(-104006577/500000000 : ℝ)|=(104006577/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034549479/2000000000 : ℝ)|^4247 ≤ (10488317560719/25000000000000 : ℝ)^3223
        have hw : |(1034549479/2000000000 : ℝ)|=(1034549479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5493610963/10000000000 : ℝ)|^4247 ≤ (22707874784547/50000000000000 : ℝ)^3223
        have hw : |(5493610963/10000000000 : ℝ)|=(5493610963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s2_5 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660831863/1250000000 : ℝ)*x 0 + (-1925603803/10000000000 : ℝ)*x 1 + (549361111/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660831863/1250000000 : ℝ)^4247 ≤ (5396858395871/12500000000000 : ℝ)^3223 := by
    have hnat : (660831863 : ℕ)^4247*12500000000000^3223 ≤ 5396858395871^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660831863 1250000000 5396858395871 12500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1925603803/10000000000 : ℝ)^4247 ≤ (5704690823237/50000000000000 : ℝ)^3223 := by
    have hnat : (1925603803 : ℕ)^4247*50000000000000^3223 ≤ 5704690823237^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925603803 10000000000 5704690823237 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549361111/1000000000 : ℝ)^4247 ≤ (908315023409/2000000000000 : ℝ)^3223 := by
    have hnat : (549361111 : ℕ)^4247*2000000000000^3223 ≤ 908315023409^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549361111 1000000000 908315023409 2000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660831863/1250000000 : ℝ), (-1925603803/10000000000 : ℝ), (549361111/1000000000 : ℝ)] ![(5396858395871/12500000000000 : ℝ), (5704690823237/50000000000000 : ℝ), (908315023409/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660831863/1250000000 : ℝ)|^4247 ≤ (5396858395871/12500000000000 : ℝ)^3223
        have hw : |(660831863/1250000000 : ℝ)|=(660831863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1925603803/10000000000 : ℝ)|^4247 ≤ (5704690823237/50000000000000 : ℝ)^3223
        have hw : |(-1925603803/10000000000 : ℝ)|=(1925603803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549361111/1000000000 : ℝ)|^4247 ≤ (908315023409/2000000000000 : ℝ)^3223
        have hw : |(549361111/1000000000 : ℝ)|=(549361111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s2_6 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132166377/250000000 : ℝ)*x 0 + (5493610971/10000000000 : ℝ)*x 1 + (-385120751/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132166377/250000000 : ℝ)^4247 ≤ (10793717265247/25000000000000 : ℝ)^3223 := by
    have hnat : (132166377 : ℕ)^4247*25000000000000^3223 ≤ 10793717265247^3223*250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132166377 250000000 10793717265247 25000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493610971/10000000000 : ℝ)^4247 ≤ (22707874828121/50000000000000 : ℝ)^3223 := by
    have hnat : (5493610971 : ℕ)^4247*50000000000000^3223 ≤ 22707874828121^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493610971 10000000000 22707874828121 50000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385120751/2000000000 : ℝ)^4247 ≤ (11409381271709/100000000000000 : ℝ)^3223 := by
    have hnat : (385120751 : ℕ)^4247*100000000000000^3223 ≤ 11409381271709^3223*2000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385120751 2000000000 11409381271709 100000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132166377/250000000 : ℝ), (5493610971/10000000000 : ℝ), (-385120751/2000000000 : ℝ)] ![(10793717265247/25000000000000 : ℝ), (22707874828121/50000000000000 : ℝ), (11409381271709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132166377/250000000 : ℝ)|^4247 ≤ (10793717265247/25000000000000 : ℝ)^3223
        have hw : |(132166377/250000000 : ℝ)|=(132166377/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493610971/10000000000 : ℝ)|^4247 ≤ (22707874828121/50000000000000 : ℝ)^3223
        have hw : |(5493610971/10000000000 : ℝ)|=(5493610971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-385120751/2000000000 : ℝ)|^4247 ≤ (11409381271709/100000000000000 : ℝ)^3223
        have hw : |(-385120751/2000000000 : ℝ)|=(385120751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1287_s2_7 (p : ℝ) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (433356629/1000000000 : ℝ)*x 0 + (4674773441/10000000000 : ℝ)*x 1 + (502072683/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433356629/1000000000 : ℝ)^4247 ≤ (6645004464403/20000000000000 : ℝ)^3223 := by
    have hnat : (433356629 : ℕ)^4247*20000000000000^3223 ≤ 6645004464403^3223*1000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433356629 1000000000 6645004464403 20000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4674773441/10000000000 : ℝ)^4247 ≤ (1835726952991/5000000000000 : ℝ)^3223 := by
    have hnat : (4674773441 : ℕ)^4247*5000000000000^3223 ≤ 1835726952991^3223*10000000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4674773441 10000000000 1835726952991 5000000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502072683/1250000000 : ℝ)^4247 ≤ (3757554826411/12500000000000 : ℝ)^3223 := by
    have hnat : (502072683 : ℕ)^4247*12500000000000^3223 ≤ 3757554826411^3223*1250000000^4247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502072683 1250000000 3757554826411 12500000000000 4247 3223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4247/1024 : ℝ)) 4247 3223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433356629/1000000000 : ℝ), (4674773441/10000000000 : ℝ), (502072683/1250000000 : ℝ)] ![(6645004464403/20000000000000 : ℝ), (1835726952991/5000000000000 : ℝ), (3757554826411/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433356629/1000000000 : ℝ)|^4247 ≤ (6645004464403/20000000000000 : ℝ)^3223
        have hw : |(433356629/1000000000 : ℝ)|=(433356629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4674773441/10000000000 : ℝ)|^4247 ≤ (1835726952991/5000000000000 : ℝ)^3223
        have hw : |(4674773441/10000000000 : ℝ)|=(4674773441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502072683/1250000000 : ℝ)|^4247 ≤ (3757554826411/12500000000000 : ℝ)^3223
        have hw : |(502072683/1250000000 : ℝ)|=(502072683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1287_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19891/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2367/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (817/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19891/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19891/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19891/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19891/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19891/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19891/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6359/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (546060125017213/50000000000000000000 : ℝ) := by
    have hpowers : (6359/100000 : ℝ)^2123 ≤ (546060125017213/50000000000000000000 : ℝ)^512 := by
      have hnat : (6359 : ℕ)^2123*50000000000000000000^512 ≤ 546060125017213^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6359 100000 546060125017213 50000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6359/100000 : ℝ)) (X := (546060125017213/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hpowhi : (19891/100000 : ℝ) ^ (2123/512 : ℝ) ≤ (123563619804811299/100000000000000000000 : ℝ) := by
    have hpowers : (19891/100000 : ℝ)^2123 ≤ (123563619804811299/100000000000000000000 : ℝ)^512 := by
      have hnat : (19891 : ℕ)^2123*100000000000000000000^512 ≤ 123563619804811299^512*100000^2123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19891 100000 123563619804811299 100000000000000000000 2123 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19891/100000 : ℝ)) (X := (123563619804811299/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000546060125017213/25000000000000000000 : ℝ) ≤ (2000010535297863/2000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (25000546060125017213/25000000000000000000 : ℝ)^512 ≤ (2000010535297863/2000000000000000 : ℝ)^2123 := by
      have hnat : (25000546060125017213 : ℕ)^512*2000000000000000^2123 ≤ 2000010535297863^2123*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000546060125017213 25000000000000000000 2000010535297863 2000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000010535297863/2000000000000000 : ℝ)) (X := (25000546060125017213/25000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (4004986229602193829/4000000000000000000 : ℝ) ≤ (10003004878692271/10000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (4004986229602193829/4000000000000000000 : ℝ)^512 ≤ (10003004878692271/10000000000000000 : ℝ)^2123 := by
      have hnat : (4004986229602193829 : ℕ)^512*10000000000000000^2123 ≤ 10003004878692271^2123*4000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4004986229602193829 4000000000000000000 10003004878692271 10000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003004878692271/10000000000000000 : ℝ)) (X := (4004986229602193829/4000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50123563619804811299/50000000000000000000 : ℝ) ≤ (10005957080895227/10000000000000000 : ℝ) ^ (2123/512 : ℝ) := by
    have hpowers : (50123563619804811299/50000000000000000000 : ℝ)^512 ≤ (10005957080895227/10000000000000000 : ℝ)^2123 := by
      have hnat : (50123563619804811299 : ℕ)^512*10000000000000000^2123 ≤ 10005957080895227^2123*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50123563619804811299 50000000000000000000 10005957080895227 10000000000000000 512 2123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005957080895227/10000000000000000 : ℝ)) (X := (50123563619804811299/50000000000000000000 : ℝ)) (by norm_num) 2123 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(546060125017213/50000000000000000000 : ℝ) ≤ ((33820791677659054043/33830000000000000000 : ℝ)+2*(738050550739/338300000000000 : ℝ)*(6359/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (33820791677659054043/33830000000000000000 : ℝ)+2*(738050550739/338300000000000 : ℝ)*(6359/100000 : ℝ)=(2000010535297863/2000000000000000 : ℝ) by norm_num, show 1+2*(546060125017213/50000000000000000000 : ℝ)=(25000546060125017213/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(123563619804811299/100000000000000000000 : ℝ)+(546060125017213/50000000000000000000 : ℝ) ≤ ((33820791677659054043/33830000000000000000 : ℝ)+(738050550739/338300000000000 : ℝ)*((19891/100000 : ℝ)+(6359/100000 : ℝ)))^(2123/512 : ℝ) := by
    rw [show (33820791677659054043/33830000000000000000 : ℝ)+(738050550739/338300000000000 : ℝ)*((19891/100000 : ℝ)+(6359/100000 : ℝ))=(10003004878692271/10000000000000000 : ℝ) by norm_num, show 1+(123563619804811299/100000000000000000000 : ℝ)+(546060125017213/50000000000000000000 : ℝ)=(4004986229602193829/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(123563619804811299/100000000000000000000 : ℝ) ≤ ((33820791677659054043/33830000000000000000 : ℝ)+2*(738050550739/338300000000000 : ℝ)*(19891/100000 : ℝ))^(2123/512 : ℝ) := by
    rw [show (33820791677659054043/33830000000000000000 : ℝ)+2*(738050550739/338300000000000 : ℝ)*(19891/100000 : ℝ)=(10005957080895227/10000000000000000 : ℝ) by norm_num, show 1+2*(123563619804811299/100000000000000000000 : ℝ)=(50123563619804811299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33820791677659054043/33830000000000000000 : ℝ)*(X 1 0+X 2 0)+(738050550739/338300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (6359/100000 : ℝ)) (hi := (19891/100000 : ℝ)) (c := (33820791677659054043/33830000000000000000 : ℝ)) (alpha := (738050550739/338300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33820791677659054043/33830000000000000000 : ℝ)*(X 0 1+X 2 1)+(738050550739/338300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (6359/100000 : ℝ)) (hi := (19891/100000 : ℝ)) (c := (33820791677659054043/33830000000000000000 : ℝ)) (alpha := (738050550739/338300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33820791677659054043/33830000000000000000 : ℝ)*(X 0 2+X 1 2)+(738050550739/338300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2123/512 : ℝ)) (lo := (6359/100000 : ℝ)) (hi := (19891/100000 : ℝ)) (c := (33820791677659054043/33830000000000000000 : ℝ)) (alpha := (738050550739/338300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-520011857/2500000000 : ℝ)*X 0 0+(1099160623/2000000000 : ℝ)*X 0 1+(517057561/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((671245197/1250000000 : ℝ)*X 1 0+(-2248639379/10000000000 : ℝ)*X 1 1+(2585288019/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335622613/625000000 : ℝ)*X 2 0+(103411513/200000000 : ℝ)*X 2 1+(-2248639579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((541674231/1250000000 : ℝ)*X 0 0+(4012080093/10000000000 : ℝ)*X 0 1+(4679229833/10000000000 : ℝ)*X 0 2+(541674231/1250000000 : ℝ)*X 1 0+(4012080093/10000000000 : ℝ)*X 1 1+(4679229833/10000000000 : ℝ)*X 1 2+(541674231/1250000000 : ℝ)*X 2 0+(4012080093/10000000000 : ℝ)*X 2 1+(4679229833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-104006577/500000000 : ℝ)*X 0 0+(1034549479/2000000000 : ℝ)*X 0 1+(5493610963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660831863/1250000000 : ℝ)*X 1 0+(-1925603803/10000000000 : ℝ)*X 1 1+(549361111/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132166377/250000000 : ℝ)*X 2 0+(5493610971/10000000000 : ℝ)*X 2 1+(-385120751/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((433356629/1000000000 : ℝ)*X 0 0+(4674773441/10000000000 : ℝ)*X 0 1+(502072683/1250000000 : ℝ)*X 0 2+(433356629/1000000000 : ℝ)*X 1 0+(4674773441/10000000000 : ℝ)*X 1 1+(502072683/1250000000 : ℝ)*X 1 2+(433356629/1000000000 : ℝ)*X 2 0+(4674773441/10000000000 : ℝ)*X 2 1+(502072683/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1287_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (275950124182579971574201137/338300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1035587061/100000000000000 : ℝ)*(base19) + (21411291/2000000000000 : ℝ)*(base23) + (26276129/50000000000000 : ℝ)*(lower2) + (408548693/100000000000000 : ℝ)*(upper3) + (217935487/100000000000000 : ℝ)*(upper5) + (457372453385749/20000000000000 : ℝ)*(major0) + (457372453385749/20000000000000 : ℝ)*(major1) + (457372453385749/20000000000000 : ℝ)*(major2) + (1537390109182999/50000000000000 : ℝ)*(sp0) + (307478609165411/10000000000000 : ℝ)*(sp1) + (3074786056676621/100000000000000 : ℝ)*(sp2) + (749462256358323/50000000000000 : ℝ)*(sp3) + (6908875173/100000000000000 : ℝ)*(sp4) + (6433354889/50000000000000 : ℝ)*(sp7) + (59957495177057/4000000000000 : ℝ)*(f.failure) + (768696781810293/25000000000000 : ℝ)*(f.sum) + (8786672265401/3383000000000000000000000000 : ℝ)*base66 + (8334293974443533207/676600000000000000000000000000000 : ℝ)*base67 + (2808540199910733207/676600000000000000000000000000000 : ℝ)*base69 + (9339577792207333207/676600000000000000000000000000000 : ℝ)*base71 + (4381423086373/3383000000000000000000000000 : ℝ)*base73 + (4671364926954133207/676600000000000000000000000000000 : ℝ)*base75 + (412508320354533207/676600000000000000000000000000000 : ℝ)*base77 + (7703384403696533207/676600000000000000000000000000000 : ℝ)*base79 + (4534900389239/1691500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (266287/100000000000000000000 : ℝ)*base89 + (266287/100000000000000000000 : ℝ)*base91 + (266287/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79407803848328392817453541/42287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90137849/25000000000000 : ℝ)*(base19) + (594152133/100000000000000 : ℝ)*(base23) + (18858283/25000000000000 : ℝ)*(upper3) + (45508923/100000000000000 : ℝ)*(lower4) + (115897574768271/5000000000000 : ℝ)*(major0) + (115897574768271/5000000000000 : ℝ)*(major1) + (115897574768271/5000000000000 : ℝ)*(major2) + (4112841053/100000000000000 : ℝ)*(sp1) + (3445009787/50000000000000 : ℝ)*(sp2) + (366307141/100000000000000 : ℝ)*(sp3) + (779146982578531/25000000000000 : ℝ)*(sp4) + (779145864230419/25000000000000 : ℝ)*(sp5) + (3116580446142417/100000000000000 : ℝ)*(sp6) + (379828657878993/25000000000000 : ℝ)*(sp7) + (1519314997823113/100000000000000 : ℝ)*(f.failure) + (779146982578531/25000000000000 : ℝ)*(f.sum) + (828879608793/845750000000000000000000000 : ℝ)*base65 + (1141353157500819653/169150000000000000000000000000000 : ℝ)*base67 + (812378206199619653/169150000000000000000000000000000 : ℝ)*base69 + (511424968835569653/169150000000000000000000000000000 : ℝ)*base71 + (344136322263/1691500000000000000000000000 : ℝ)*base73 + (1010681075422680347/169150000000000000000000000000000 : ℝ)*base76 + (509009588027569653/169150000000000000000000000000000 : ℝ)*base77 + (1554971757483769653/169150000000000000000000000000000 : ℝ)*base79 + (627249601709/845750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1770183/2500000000000000000000 : ℝ)*base89 + (1770183/2500000000000000000000 : ℝ)*base91 + (1770183/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1287_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19891/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2367/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (817/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1287_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1287_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2367/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (817/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1287_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1287_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1287_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2123/512 : ℝ) ≤ p) (hpb : p ≤ (4247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38141391/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2367/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (817/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1287_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

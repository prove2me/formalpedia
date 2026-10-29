-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1494_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:49.744435+00:00
-- url     : https://prove2.me/submissions/149b00e4-e24d-45a9-9ee2-bd18ae94c2d4

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
theorem support_rectangle_w1494_s3_0 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-947161903/5000000000 : ℝ)*x 0 + (1359901687/2500000000 : ℝ)*x 1 + (1303264823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947161903/5000000000 : ℝ)^4485 ≤ (1447391029011/12500000000000 : ℝ)^3461 := by
    have hnat : (947161903 : ℕ)^4485*12500000000000^3461 ≤ 1447391029011^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947161903 5000000000 1447391029011 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359901687/2500000000 : ℝ)^4485 ≤ (45428701662731/100000000000000 : ℝ)^3461 := by
    have hnat : (1359901687 : ℕ)^4485*100000000000000^3461 ≤ 45428701662731^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359901687 2500000000 45428701662731 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303264823/2500000000 : ℝ)^4485 ≤ (21496085046779/50000000000000 : ℝ)^3461 := by
    have hnat : (1303264823 : ℕ)^4485*50000000000000^3461 ≤ 21496085046779^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303264823 2500000000 21496085046779 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-947161903/5000000000 : ℝ), (1359901687/2500000000 : ℝ), (1303264823/2500000000 : ℝ)] ![(1447391029011/12500000000000 : ℝ), (45428701662731/100000000000000 : ℝ), (21496085046779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-947161903/5000000000 : ℝ)|^4485 ≤ (1447391029011/12500000000000 : ℝ)^3461
        have hw : |(-947161903/5000000000 : ℝ)|=(947161903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359901687/2500000000 : ℝ)|^4485 ≤ (45428701662731/100000000000000 : ℝ)^3461
        have hw : |(1359901687/2500000000 : ℝ)|=(1359901687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303264823/2500000000 : ℝ)|^4485 ≤ (21496085046779/50000000000000 : ℝ)^3461
        have hw : |(1303264823/2500000000 : ℝ)|=(1303264823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s3_1 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353620543/10000000000 : ℝ)*x 0 + (-2010490367/10000000000 : ℝ)*x 1 + (5213059481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353620543/10000000000 : ℝ)^4485 ≤ (8900061722959/20000000000000 : ℝ)^3461 := by
    have hnat : (5353620543 : ℕ)^4485*20000000000000^3461 ≤ 8900061722959^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353620543 10000000000 8900061722959 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010490367/10000000000 : ℝ)^4485 ≤ (6253759628287/50000000000000 : ℝ)^3461 := by
    have hnat : (2010490367 : ℕ)^4485*50000000000000^3461 ≤ 6253759628287^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010490367 10000000000 6253759628287 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5213059481/10000000000 : ℝ)^4485 ≤ (42992172113409/100000000000000 : ℝ)^3461 := by
    have hnat : (5213059481 : ℕ)^4485*100000000000000^3461 ≤ 42992172113409^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213059481 10000000000 42992172113409 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353620543/10000000000 : ℝ), (-2010490367/10000000000 : ℝ), (5213059481/10000000000 : ℝ)] ![(8900061722959/20000000000000 : ℝ), (6253759628287/50000000000000 : ℝ), (42992172113409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353620543/10000000000 : ℝ)|^4485 ≤ (8900061722959/20000000000000 : ℝ)^3461
        have hw : |(5353620543/10000000000 : ℝ)|=(5353620543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2010490367/10000000000 : ℝ)|^4485 ≤ (6253759628287/50000000000000 : ℝ)^3461
        have hw : |(-2010490367/10000000000 : ℝ)|=(2010490367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5213059481/10000000000 : ℝ)|^4485 ≤ (42992172113409/100000000000000 : ℝ)^3461
        have hw : |(5213059481/10000000000 : ℝ)|=(5213059481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s3_2 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353620769/10000000000 : ℝ)*x 0 + (2606529551/5000000000 : ℝ)*x 1 + (-1005245283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353620769/10000000000 : ℝ)^4485 ≤ (8900062209831/20000000000000 : ℝ)^3461 := by
    have hnat : (5353620769 : ℕ)^4485*20000000000000^3461 ≤ 8900062209831^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353620769 10000000000 8900062209831 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606529551/5000000000 : ℝ)^4485 ≤ (2149608403151/5000000000000 : ℝ)^3461 := by
    have hnat : (2606529551 : ℕ)^4485*5000000000000^3461 ≤ 2149608403151^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606529551 5000000000 2149608403151 5000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005245283/5000000000 : ℝ)^4485 ≤ (2501504172173/20000000000000 : ℝ)^3461 := by
    have hnat : (1005245283 : ℕ)^4485*20000000000000^3461 ≤ 2501504172173^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005245283 5000000000 2501504172173 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353620769/10000000000 : ℝ), (2606529551/5000000000 : ℝ), (-1005245283/5000000000 : ℝ)] ![(8900062209831/20000000000000 : ℝ), (2149608403151/5000000000000 : ℝ), (2501504172173/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353620769/10000000000 : ℝ)|^4485 ≤ (8900062209831/20000000000000 : ℝ)^3461
        have hw : |(5353620769/10000000000 : ℝ)|=(5353620769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606529551/5000000000 : ℝ)|^4485 ≤ (2149608403151/5000000000000 : ℝ)^3461
        have hw : |(2606529551/5000000000 : ℝ)|=(2606529551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1005245283/5000000000 : ℝ)|^4485 ≤ (2501504172173/20000000000000 : ℝ)^3461
        have hw : |(-1005245283/5000000000 : ℝ)|=(1005245283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s3_3 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138922461/5000000000 : ℝ)*x 0 + (2015359663/5000000000 : ℝ)*x 1 + (4537925767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138922461/5000000000 : ℝ)^4485 ≤ (2079678741379/6250000000000 : ℝ)^3461 := by
    have hnat : (2138922461 : ℕ)^4485*6250000000000^3461 ≤ 2079678741379^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138922461 5000000000 2079678741379 6250000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015359663/5000000000 : ℝ)^4485 ≤ (6161093260411/20000000000000 : ℝ)^3461 := by
    have hnat : (2015359663 : ℕ)^4485*20000000000000^3461 ≤ 6161093260411^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015359663 5000000000 6161093260411 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4537925767/10000000000 : ℝ)^4485 ≤ (4489959227319/12500000000000 : ℝ)^3461 := by
    have hnat : (4537925767 : ℕ)^4485*12500000000000^3461 ≤ 4489959227319^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537925767 10000000000 4489959227319 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138922461/5000000000 : ℝ), (2015359663/5000000000 : ℝ), (4537925767/10000000000 : ℝ)] ![(2079678741379/6250000000000 : ℝ), (6161093260411/20000000000000 : ℝ), (4489959227319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138922461/5000000000 : ℝ)|^4485 ≤ (2079678741379/6250000000000 : ℝ)^3461
        have hw : |(2138922461/5000000000 : ℝ)|=(2138922461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015359663/5000000000 : ℝ)|^4485 ≤ (6161093260411/20000000000000 : ℝ)^3461
        have hw : |(2015359663/5000000000 : ℝ)|=(2015359663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4537925767/10000000000 : ℝ)|^4485 ≤ (4489959227319/12500000000000 : ℝ)^3461
        have hw : |(4537925767/10000000000 : ℝ)|=(4537925767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s3_4 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1894355991/10000000000 : ℝ)*x 0 + (5214261561/10000000000 : ℝ)*x 1 + (5438395879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1894355991/10000000000 : ℝ)^4485 ≤ (1157938317157/10000000000000 : ℝ)^3461 := by
    have hnat : (1894355991 : ℕ)^4485*10000000000000^3461 ≤ 1157938317157^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894355991 10000000000 1157938317157 10000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214261561/10000000000 : ℝ)^4485 ≤ (21502509616113/50000000000000 : ℝ)^3461 := by
    have hnat : (5214261561 : ℕ)^4485*50000000000000^3461 ≤ 21502509616113^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214261561 10000000000 21502509616113 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438395879/10000000000 : ℝ)^4485 ≤ (45415597582981/100000000000000 : ℝ)^3461 := by
    have hnat : (5438395879 : ℕ)^4485*100000000000000^3461 ≤ 45415597582981^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438395879 10000000000 45415597582981 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1894355991/10000000000 : ℝ), (5214261561/10000000000 : ℝ), (5438395879/10000000000 : ℝ)] ![(1157938317157/10000000000000 : ℝ), (21502509616113/50000000000000 : ℝ), (45415597582981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1894355991/10000000000 : ℝ)|^4485 ≤ (1157938317157/10000000000000 : ℝ)^3461
        have hw : |(-1894355991/10000000000 : ℝ)|=(1894355991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214261561/10000000000 : ℝ)|^4485 ≤ (21502509616113/50000000000000 : ℝ)^3461
        have hw : |(5214261561/10000000000 : ℝ)|=(5214261561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438395879/10000000000 : ℝ)|^4485 ≤ (45415597582981/100000000000000 : ℝ)^3461
        have hw : |(5438395879/10000000000 : ℝ)|=(5438395879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s3_5 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323578383/2500000000 : ℝ)*x 0 + (-892577061/5000000000 : ℝ)*x 1 + (5438396343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323578383/2500000000 : ℝ)^4485 ≤ (10965633161017/25000000000000 : ℝ)^3461 := by
    have hnat : (1323578383 : ℕ)^4485*25000000000000^3461 ≤ 10965633161017^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323578383 2500000000 10965633161017 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (892577061/5000000000 : ℝ)^4485 ≤ (2680466183417/25000000000000 : ℝ)^3461 := by
    have hnat : (892577061 : ℕ)^4485*25000000000000^3461 ≤ 2680466183417^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892577061 5000000000 2680466183417 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438396343/10000000000 : ℝ)^4485 ≤ (9083120520849/20000000000000 : ℝ)^3461 := by
    have hnat : (5438396343 : ℕ)^4485*20000000000000^3461 ≤ 9083120520849^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438396343 10000000000 9083120520849 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323578383/2500000000 : ℝ), (-892577061/5000000000 : ℝ), (5438396343/10000000000 : ℝ)] ![(10965633161017/25000000000000 : ℝ), (2680466183417/25000000000000 : ℝ), (9083120520849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323578383/2500000000 : ℝ)|^4485 ≤ (10965633161017/25000000000000 : ℝ)^3461
        have hw : |(1323578383/2500000000 : ℝ)|=(1323578383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-892577061/5000000000 : ℝ)|^4485 ≤ (2680466183417/25000000000000 : ℝ)^3461
        have hw : |(-892577061/5000000000 : ℝ)|=(892577061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438396343/10000000000 : ℝ)|^4485 ≤ (9083120520849/20000000000000 : ℝ)^3461
        have hw : |(5438396343/10000000000 : ℝ)|=(5438396343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s3_6 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647157397/5000000000 : ℝ)*x 0 + (2719197679/5000000000 : ℝ)*x 1 + (-1785153751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647157397/5000000000 : ℝ)^4485 ≤ (1754501847719/4000000000000 : ℝ)^3461 := by
    have hnat : (2647157397 : ℕ)^4485*4000000000000^3461 ≤ 1754501847719^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647157397 5000000000 1754501847719 4000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719197679/5000000000 : ℝ)^4485 ≤ (45415591944881/100000000000000 : ℝ)^3461 := by
    have hnat : (2719197679 : ℕ)^4485*100000000000000^3461 ≤ 45415591944881^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719197679 5000000000 45415591944881 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1785153751/10000000000 : ℝ)^4485 ≤ (10721861846119/100000000000000 : ℝ)^3461 := by
    have hnat : (1785153751 : ℕ)^4485*100000000000000^3461 ≤ 10721861846119^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785153751 10000000000 10721861846119 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647157397/5000000000 : ℝ), (2719197679/5000000000 : ℝ), (-1785153751/10000000000 : ℝ)] ![(1754501847719/4000000000000 : ℝ), (45415591944881/100000000000000 : ℝ), (10721861846119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647157397/5000000000 : ℝ)|^4485 ≤ (1754501847719/4000000000000 : ℝ)^3461
        have hw : |(2647157397/5000000000 : ℝ)|=(2647157397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719197679/5000000000 : ℝ)|^4485 ≤ (45415591944881/100000000000000 : ℝ)^3461
        have hw : |(2719197679/5000000000 : ℝ)|=(2719197679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1785153751/10000000000 : ℝ)|^4485 ≤ (10721861846119/100000000000000 : ℝ)^3461
        have hw : |(-1785153751/10000000000 : ℝ)|=(1785153751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s3_7 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138958891/5000000000 : ℝ)*x 0 + (4535233491/10000000000 : ℝ)*x 1 + (201671651/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138958891/5000000000 : ℝ)^4485 ≤ (6655118855673/20000000000000 : ℝ)^3461 := by
    have hnat : (2138958891 : ℕ)^4485*20000000000000^3461 ≤ 6655118855673^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138958891 5000000000 6655118855673 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535233491/10000000000 : ℝ)^4485 ≤ (1435682423311/4000000000000 : ℝ)^3461 := by
    have hnat : (4535233491 : ℕ)^4485*4000000000000^3461 ≤ 1435682423311^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535233491 10000000000 1435682423311 4000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201671651/500000000 : ℝ)^4485 ≤ (770808628049/2500000000000 : ℝ)^3461 := by
    have hnat : (201671651 : ℕ)^4485*2500000000000^3461 ≤ 770808628049^3461*500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201671651 500000000 770808628049 2500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138958891/5000000000 : ℝ), (4535233491/10000000000 : ℝ), (201671651/500000000 : ℝ)] ![(6655118855673/20000000000000 : ℝ), (1435682423311/4000000000000 : ℝ), (770808628049/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138958891/5000000000 : ℝ)|^4485 ≤ (6655118855673/20000000000000 : ℝ)^3461
        have hw : |(2138958891/5000000000 : ℝ)|=(2138958891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535233491/10000000000 : ℝ)|^4485 ≤ (1435682423311/4000000000000 : ℝ)^3461
        have hw : |(4535233491/10000000000 : ℝ)|=(4535233491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201671651/500000000 : ℝ)|^4485 ≤ (770808628049/2500000000000 : ℝ)^3461
        have hw : |(201671651/500000000 : ℝ)|=(201671651/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1494_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10767/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15563/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5151/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5151/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5151/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5151/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5151/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5151/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5151/50000 : ℝ) ^ (4483/1024 : ℝ) ≤ (4771335225078277/100000000000000000000 : ℝ) := by
    have hpowers : (5151/50000 : ℝ)^4483 ≤ (4771335225078277/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5151 : ℕ)^4483*100000000000000000000^1024 ≤ 4771335225078277^1024*50000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5151 50000 4771335225078277 100000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5151/50000 : ℝ)) (X := (4771335225078277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16069/100000 : ℝ) ^ (4483/1024 : ℝ) ≤ (33409887826786937/100000000000000000000 : ℝ) := by
    have hpowers : (16069/100000 : ℝ)^4483 ≤ (33409887826786937/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16069 : ℕ)^4483*100000000000000000000^1024 ≤ 33409887826786937^1024*100000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16069 100000 33409887826786937 100000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16069/100000 : ℝ)) (X := (33409887826786937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004771335225078277/50000000000000000000 : ℝ) ≤ (10000217964194041/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (50004771335225078277/50000000000000000000 : ℝ)^1024 ≤ (10000217964194041/10000000000000000 : ℝ)^4483 := by
      have hnat : (50004771335225078277 : ℕ)^1024*10000000000000000^4483 ≤ 10000217964194041^4483*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004771335225078277 50000000000000000000 10000217964194041 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000217964194041/10000000000000000 : ℝ)) (X := (50004771335225078277/50000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019090611525932607/50000000000000000000 : ℝ) ≤ (78131812509523/78125000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (50019090611525932607/50000000000000000000 : ℝ)^1024 ≤ (78131812509523/78125000000000 : ℝ)^4483 := by
      have hnat : (50019090611525932607 : ℕ)^1024*78125000000000^4483 ≤ 78131812509523^4483*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019090611525932607 50000000000000000000 78131812509523 78125000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78131812509523/78125000000000 : ℝ)) (X := (50019090611525932607/50000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033409887826786937/50000000000000000000 : ℝ) ≤ (10001526038243847/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (50033409887826786937/50000000000000000000 : ℝ)^1024 ≤ (10001526038243847/10000000000000000 : ℝ)^4483 := by
      have hnat : (50033409887826786937 : ℕ)^1024*10000000000000000^4483 ≤ 10001526038243847^4483*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033409887826786937 50000000000000000000 10001526038243847 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001526038243847/10000000000000000 : ℝ)) (X := (50033409887826786937/50000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4771335225078277/100000000000000000000 : ℝ) ≤ ((11531556244129186607/11534000000000000000 : ℝ)+2*(654037024903/576700000000000 : ℝ)*(5151/50000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (11531556244129186607/11534000000000000000 : ℝ)+2*(654037024903/576700000000000 : ℝ)*(5151/50000 : ℝ)=(10000217964194041/10000000000000000 : ℝ) by norm_num, show 1+2*(4771335225078277/100000000000000000000 : ℝ)=(50004771335225078277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33409887826786937/100000000000000000000 : ℝ)+(4771335225078277/100000000000000000000 : ℝ) ≤ ((11531556244129186607/11534000000000000000 : ℝ)+(654037024903/576700000000000 : ℝ)*((16069/100000 : ℝ)+(5151/50000 : ℝ)))^(4483/1024 : ℝ) := by
    rw [show (11531556244129186607/11534000000000000000 : ℝ)+(654037024903/576700000000000 : ℝ)*((16069/100000 : ℝ)+(5151/50000 : ℝ))=(78131812509523/78125000000000 : ℝ) by norm_num, show 1+(33409887826786937/100000000000000000000 : ℝ)+(4771335225078277/100000000000000000000 : ℝ)=(50019090611525932607/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33409887826786937/100000000000000000000 : ℝ) ≤ ((11531556244129186607/11534000000000000000 : ℝ)+2*(654037024903/576700000000000 : ℝ)*(16069/100000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (11531556244129186607/11534000000000000000 : ℝ)+2*(654037024903/576700000000000 : ℝ)*(16069/100000 : ℝ)=(10001526038243847/10000000000000000 : ℝ) by norm_num, show 1+2*(33409887826786937/100000000000000000000 : ℝ)=(50033409887826786937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11531556244129186607/11534000000000000000 : ℝ)*(X 1 0+X 2 0)+(654037024903/576700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (16069/100000 : ℝ)) (c := (11531556244129186607/11534000000000000000 : ℝ)) (alpha := (654037024903/576700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11531556244129186607/11534000000000000000 : ℝ)*(X 0 1+X 2 1)+(654037024903/576700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (16069/100000 : ℝ)) (c := (11531556244129186607/11534000000000000000 : ℝ)) (alpha := (654037024903/576700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11531556244129186607/11534000000000000000 : ℝ)*(X 0 2+X 1 2)+(654037024903/576700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (16069/100000 : ℝ)) (c := (11531556244129186607/11534000000000000000 : ℝ)) (alpha := (654037024903/576700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-947161903/5000000000 : ℝ)*X 0 0+(1359901687/2500000000 : ℝ)*X 0 1+(1303264823/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353620543/10000000000 : ℝ)*X 1 0+(-2010490367/10000000000 : ℝ)*X 1 1+(5213059481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353620769/10000000000 : ℝ)*X 2 0+(2606529551/5000000000 : ℝ)*X 2 1+(-1005245283/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2138922461/5000000000 : ℝ)*X 0 0+(2015359663/5000000000 : ℝ)*X 0 1+(4537925767/10000000000 : ℝ)*X 0 2+(2138922461/5000000000 : ℝ)*X 1 0+(2015359663/5000000000 : ℝ)*X 1 1+(4537925767/10000000000 : ℝ)*X 1 2+(2138922461/5000000000 : ℝ)*X 2 0+(2015359663/5000000000 : ℝ)*X 2 1+(4537925767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1894355991/10000000000 : ℝ)*X 0 0+(5214261561/10000000000 : ℝ)*X 0 1+(5438395879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323578383/2500000000 : ℝ)*X 1 0+(-892577061/5000000000 : ℝ)*X 1 1+(5438396343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647157397/5000000000 : ℝ)*X 2 0+(2719197679/5000000000 : ℝ)*X 2 1+(-1785153751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2138958891/5000000000 : ℝ)*X 0 0+(4535233491/10000000000 : ℝ)*X 0 1+(201671651/500000000 : ℝ)*X 0 2+(2138958891/5000000000 : ℝ)*X 1 0+(4535233491/10000000000 : ℝ)*X 1 1+(201671651/500000000 : ℝ)*X 1 2+(2138958891/5000000000 : ℝ)*X 2 0+(4535233491/10000000000 : ℝ)*X 2 1+(201671651/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92349785416334728484118393/18021875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1685827869/100000000000000 : ℝ)*(base19) + (1655391567/100000000000000 : ℝ)*(base23) + (22932433/6250000000000 : ℝ)*(upper3) + (725337/625000000000 : ℝ)*(upper4) + (60503853/100000000000000 : ℝ)*(upper5) + (199554514212083/6250000000000 : ℝ)*(major0) + (199554514212083/6250000000000 : ℝ)*(major1) + (199554514212083/6250000000000 : ℝ)*(major2) + (1103528671500107/25000000000000 : ℝ)*(sp0) + (551767029033181/12500000000000 : ℝ)*(sp1) + (17656545050807/400000000000 : ℝ)*(sp2) + (246449114324903/12500000000000 : ℝ)*(sp3) + (23232092889/100000000000000 : ℝ)*(sp4) + (13451283569/100000000000000 : ℝ)*(sp7) + (985803182941397/50000000000000 : ℝ)*(f.failure) + (4414137918093317/100000000000000 : ℝ)*(f.sum) + (119273100536819/28835000000000000000000000000 : ℝ)*base65 + (134376664055997619/72087500000000000000000000000000 : ℝ)*base68 + (743335410776910119/72087500000000000000000000000000 : ℝ)*base70 + (75677482099527381/72087500000000000000000000000000 : ℝ)*base71 + (8937545467039/28835000000000000000000000000 : ℝ)*base73 + (759261780078497619/72087500000000000000000000000000 : ℝ)*base76 + (429709777297497619/72087500000000000000000000000000 : ℝ)*base78 + (60487021754860119/72087500000000000000000000000000 : ℝ)*base80 + (544143378831/1802187500000000000000000000 : ℝ)*base82 + (39503377/2500000000000000000000 : ℝ)*base89 + (39503377/2500000000000000000000 : ℝ)*base91 + (39503377/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (712080426528284806066197693/57670000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (519506739/50000000000000 : ℝ)*(base19) + (296085241/12500000000000 : ℝ)*(base23) + (8789387/10000000000000 : ℝ)*(lower4) + (188257407/100000000000000 : ℝ)*(upper5) + (322723298812789/10000000000000 : ℝ)*(major0) + (322723298812789/10000000000000 : ℝ)*(major1) + (322723298812789/10000000000000 : ℝ)*(major2) + (522960159/5000000000000 : ℝ)*(sp0) + (8135917337/20000000000000 : ℝ)*(sp1) + (49619608769/100000000000000 : ℝ)*(sp2) + (1115407721565777/25000000000000 : ℝ)*(sp4) + (35692797014929/800000000000 : ℝ)*(sp5) + (446158935717559/10000000000000 : ℝ)*(sp6) + (996412109603041/50000000000000 : ℝ)*(sp7) + (996412109603041/50000000000000 : ℝ)*(f.failure) + (278852584091643/6250000000000 : ℝ)*(f.sum) + (7451880906169/2883500000000000000000000000 : ℝ)*base66 + (912654610231856923/115340000000000000000000000000000 : ℝ)*base67 + (1669738799083576923/115340000000000000000000000000000 : ℝ)*base69 + (1386658055426596923/115340000000000000000000000000000 : ℝ)*base71 + (2512523405261/1153400000000000000000000000 : ℝ)*base74 + (1499115083568456923/115340000000000000000000000000000 : ℝ)*base75 + (1656504247692156923/115340000000000000000000000000000 : ℝ)*base77 + (2071414871795656923/115340000000000000000000000000000 : ℝ)*base79 + (677428544951/2883500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (42552019/2500000000000000000000 : ℝ)*base90 + (42552019/2500000000000000000000 : ℝ)*base92 + (42552019/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1494_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15563/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1494_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1494_s4_0 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-473715019/2500000000 : ℝ)*x 0 + (543610431/1000000000 : ℝ)*x 1 + (5216207981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473715019/2500000000 : ℝ)^4485 ≤ (1158337622891/10000000000000 : ℝ)^3461 := by
    have hnat : (473715019 : ℕ)^4485*10000000000000^3461 ≤ 1158337622891^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473715019 2500000000 1158337622891 10000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543610431/1000000000 : ℝ)^4485 ≤ (453908004811/1000000000000 : ℝ)^3461 := by
    have hnat : (543610431 : ℕ)^4485*1000000000000^3461 ≤ 453908004811^3461*1000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543610431 1000000000 453908004811 1000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216207981/10000000000 : ℝ)^4485 ≤ (4302582327413/10000000000000 : ℝ)^3461 := by
    have hnat : (5216207981 : ℕ)^4485*10000000000000^3461 ≤ 4302582327413^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216207981 10000000000 4302582327413 10000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473715019/2500000000 : ℝ), (543610431/1000000000 : ℝ), (5216207981/10000000000 : ℝ)] ![(1158337622891/10000000000000 : ℝ), (453908004811/1000000000000 : ℝ), (4302582327413/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473715019/2500000000 : ℝ)|^4485 ≤ (1158337622891/10000000000000 : ℝ)^3461
        have hw : |(-473715019/2500000000 : ℝ)|=(473715019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543610431/1000000000 : ℝ)|^4485 ≤ (453908004811/1000000000000 : ℝ)^3461
        have hw : |(543610431/1000000000 : ℝ)|=(543610431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216207981/10000000000 : ℝ)|^4485 ≤ (4302582327413/10000000000000 : ℝ)^3461
        have hw : |(5216207981/10000000000 : ℝ)|=(5216207981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s4_1 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26763541/50000000 : ℝ)*x 0 + (-2007533629/10000000000 : ℝ)*x 1 + (5216208657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26763541/50000000 : ℝ)^4485 ≤ (44490481557681/100000000000000 : ℝ)^3461 := by
    have hnat : (26763541 : ℕ)^4485*100000000000000^3461 ≤ 44490481557681^3461*50000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26763541 50000000 44490481557681 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007533629/10000000000 : ℝ)^4485 ≤ (12483687922951/100000000000000 : ℝ)^3461 := by
    have hnat : (2007533629 : ℕ)^4485*100000000000000^3461 ≤ 12483687922951^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007533629 10000000000 12483687922951 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216208657/10000000000 : ℝ)^4485 ≤ (43025830499861/100000000000000 : ℝ)^3461 := by
    have hnat : (5216208657 : ℕ)^4485*100000000000000^3461 ≤ 43025830499861^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216208657 10000000000 43025830499861 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26763541/50000000 : ℝ), (-2007533629/10000000000 : ℝ), (5216208657/10000000000 : ℝ)] ![(44490481557681/100000000000000 : ℝ), (12483687922951/100000000000000 : ℝ), (43025830499861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26763541/50000000 : ℝ)|^4485 ≤ (44490481557681/100000000000000 : ℝ)^3461
        have hw : |(26763541/50000000 : ℝ)|=(26763541/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2007533629/10000000000 : ℝ)|^4485 ≤ (12483687922951/100000000000000 : ℝ)^3461
        have hw : |(-2007533629/10000000000 : ℝ)|=(2007533629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216208657/10000000000 : ℝ)|^4485 ≤ (43025830499861/100000000000000 : ℝ)^3461
        have hw : |(5216208657/10000000000 : ℝ)|=(5216208657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s4_2 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334544273/625000000 : ℝ)*x 0 + (1304051981/2500000000 : ℝ)*x 1 + (-1003767189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334544273/625000000 : ℝ)^4485 ≤ (22245241683601/50000000000000 : ℝ)^3461 := by
    have hnat : (334544273 : ℕ)^4485*50000000000000^3461 ≤ 22245241683601^3461*625000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334544273 625000000 22245241683601 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304051981/2500000000 : ℝ)^4485 ≤ (43025822664859/100000000000000 : ℝ)^3461 := by
    have hnat : (1304051981 : ℕ)^4485*100000000000000^3461 ≤ 43025822664859^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304051981 2500000000 43025822664859 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003767189/5000000000 : ℝ)^4485 ≤ (1560461744823/12500000000000 : ℝ)^3461 := by
    have hnat : (1003767189 : ℕ)^4485*12500000000000^3461 ≤ 1560461744823^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003767189 5000000000 1560461744823 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334544273/625000000 : ℝ), (1304051981/2500000000 : ℝ), (-1003767189/5000000000 : ℝ)] ![(22245241683601/50000000000000 : ℝ), (43025822664859/100000000000000 : ℝ), (1560461744823/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334544273/625000000 : ℝ)|^4485 ≤ (22245241683601/50000000000000 : ℝ)^3461
        have hw : |(334544273/625000000 : ℝ)|=(334544273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304051981/2500000000 : ℝ)|^4485 ≤ (43025822664859/100000000000000 : ℝ)^3461
        have hw : |(1304051981/2500000000 : ℝ)|=(1304051981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1003767189/5000000000 : ℝ)|^4485 ≤ (1560461744823/12500000000000 : ℝ)^3461
        have hw : |(-1003767189/5000000000 : ℝ)|=(1003767189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s4_3 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278179347/10000000000 : ℝ)*x 0 + (807625649/2000000000 : ℝ)*x 1 + (1132609937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278179347/10000000000 : ℝ)^4485 ≤ (33278230839183/100000000000000 : ℝ)^3461 := by
    have hnat : (4278179347 : ℕ)^4485*100000000000000^3461 ≤ 33278230839183^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278179347 10000000000 33278230839183 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (807625649/2000000000 : ℝ)^4485 ≤ (30878863410463/100000000000000 : ℝ)^3461 := by
    have hnat : (807625649 : ℕ)^4485*100000000000000^3461 ≤ 30878863410463^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807625649 2000000000 30878863410463 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132609937/2500000000 : ℝ)^4485 ≤ (8960726432349/25000000000000 : ℝ)^3461 := by
    have hnat : (1132609937 : ℕ)^4485*25000000000000^3461 ≤ 8960726432349^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132609937 2500000000 8960726432349 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278179347/10000000000 : ℝ), (807625649/2000000000 : ℝ), (1132609937/2500000000 : ℝ)] ![(33278230839183/100000000000000 : ℝ), (30878863410463/100000000000000 : ℝ), (8960726432349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278179347/10000000000 : ℝ)|^4485 ≤ (33278230839183/100000000000000 : ℝ)^3461
        have hw : |(4278179347/10000000000 : ℝ)|=(4278179347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(807625649/2000000000 : ℝ)|^4485 ≤ (30878863410463/100000000000000 : ℝ)^3461
        have hw : |(807625649/2000000000 : ℝ)|=(807625649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132609937/2500000000 : ℝ)|^4485 ≤ (8960726432349/25000000000000 : ℝ)^3461
        have hw : |(1132609937/2500000000 : ℝ)|=(1132609937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s4_4 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1894890979/10000000000 : ℝ)*x 0 + (5217341241/10000000000 : ℝ)*x 1 + (1086992423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1894890979/10000000000 : ℝ)^4485 ≤ (11583621034063/100000000000000 : ℝ)^3461 := by
    have hnat : (1894890979 : ℕ)^4485*100000000000000^3461 ≤ 11583621034063^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894890979 10000000000 11583621034063 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217341241/10000000000 : ℝ)^4485 ≤ (21518968512741/50000000000000 : ℝ)^3461 := by
    have hnat : (5217341241 : ℕ)^4485*50000000000000^3461 ≤ 21518968512741^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217341241 10000000000 21518968512741 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086992423/2000000000 : ℝ)^4485 ≤ (22689220963501/50000000000000 : ℝ)^3461 := by
    have hnat : (1086992423 : ℕ)^4485*50000000000000^3461 ≤ 22689220963501^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086992423 2000000000 22689220963501 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1894890979/10000000000 : ℝ), (5217341241/10000000000 : ℝ), (1086992423/2000000000 : ℝ)] ![(11583621034063/100000000000000 : ℝ), (21518968512741/50000000000000 : ℝ), (22689220963501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1894890979/10000000000 : ℝ)|^4485 ≤ (11583621034063/100000000000000 : ℝ)^3461
        have hw : |(-1894890979/10000000000 : ℝ)|=(1894890979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217341241/10000000000 : ℝ)|^4485 ≤ (21518968512741/50000000000000 : ℝ)^3461
        have hw : |(5217341241/10000000000 : ℝ)|=(5217341241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086992423/2000000000 : ℝ)|^4485 ≤ (22689220963501/50000000000000 : ℝ)^3461
        have hw : |(1086992423/2000000000 : ℝ)|=(1086992423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s4_5 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323786291/2500000000 : ℝ)*x 0 + (-894390257/5000000000 : ℝ)*x 1 + (5434962003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323786291/2500000000 : ℝ)^4485 ≤ (1096786532547/2500000000000 : ℝ)^3461 := by
    have hnat : (1323786291 : ℕ)^4485*2500000000000^3461 ≤ 1096786532547^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323786291 2500000000 1096786532547 2500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894390257/5000000000 : ℝ)^4485 ≤ (10750097968051/100000000000000 : ℝ)^3461 := by
    have hnat : (894390257 : ℕ)^4485*100000000000000^3461 ≤ 10750097968051^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894390257 5000000000 10750097968051 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434962003/10000000000 : ℝ)^4485 ≤ (45378440715199/100000000000000 : ℝ)^3461 := by
    have hnat : (5434962003 : ℕ)^4485*100000000000000^3461 ≤ 45378440715199^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434962003 10000000000 45378440715199 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323786291/2500000000 : ℝ), (-894390257/5000000000 : ℝ), (5434962003/10000000000 : ℝ)] ![(1096786532547/2500000000000 : ℝ), (10750097968051/100000000000000 : ℝ), (45378440715199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323786291/2500000000 : ℝ)|^4485 ≤ (1096786532547/2500000000000 : ℝ)^3461
        have hw : |(1323786291/2500000000 : ℝ)|=(1323786291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-894390257/5000000000 : ℝ)|^4485 ≤ (10750097968051/100000000000000 : ℝ)^3461
        have hw : |(-894390257/5000000000 : ℝ)|=(894390257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434962003/10000000000 : ℝ)|^4485 ≤ (45378440715199/100000000000000 : ℝ)^3461
        have hw : |(5434962003/10000000000 : ℝ)|=(5434962003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s4_6 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295145307/10000000000 : ℝ)*x 0 + (543496173/1000000000 : ℝ)*x 1 + (-223597587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295145307/10000000000 : ℝ)^4485 ≤ (5483932854651/12500000000000 : ℝ)^3461 := by
    have hnat : (5295145307 : ℕ)^4485*12500000000000^3461 ≤ 5483932854651^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295145307 10000000000 5483932854651 12500000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543496173/1000000000 : ℝ)^4485 ≤ (4537843776143/10000000000000 : ℝ)^3461 := by
    have hnat : (543496173 : ℕ)^4485*10000000000000^3461 ≤ 4537843776143^3461*1000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543496173 1000000000 4537843776143 10000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223597587/1250000000 : ℝ)^4485 ≤ (2150019877087/20000000000000 : ℝ)^3461 := by
    have hnat : (223597587 : ℕ)^4485*20000000000000^3461 ≤ 2150019877087^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223597587 1250000000 2150019877087 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295145307/10000000000 : ℝ), (543496173/1000000000 : ℝ), (-223597587/1250000000 : ℝ)] ![(5483932854651/12500000000000 : ℝ), (4537843776143/10000000000000 : ℝ), (2150019877087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295145307/10000000000 : ℝ)|^4485 ≤ (5483932854651/12500000000000 : ℝ)^3461
        have hw : |(5295145307/10000000000 : ℝ)|=(5295145307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543496173/1000000000 : ℝ)|^4485 ≤ (4537843776143/10000000000000 : ℝ)^3461
        have hw : |(543496173/1000000000 : ℝ)|=(543496173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223597587/1250000000 : ℝ)|^4485 ≤ (2150019877087/20000000000000 : ℝ)^3461
        have hw : |(-223597587/1250000000 : ℝ)|=(223597587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s4_7 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278247729/10000000000 : ℝ)*x 0 + (4527903633/10000000000 : ℝ)*x 1 + (80813643/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278247729/10000000000 : ℝ)^4485 ≤ (33278920133847/100000000000000 : ℝ)^3461 := by
    have hnat : (4278247729 : ℕ)^4485*100000000000000^3461 ≤ 33278920133847^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278247729 10000000000 33278920133847 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4527903633/10000000000 : ℝ)^4485 ≤ (35816906727807/100000000000000 : ℝ)^3461 := by
    have hnat : (4527903633 : ℕ)^4485*100000000000000^3461 ≤ 35816906727807^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527903633 10000000000 35816906727807 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80813643/200000000 : ℝ)^4485 ≤ (7726043283633/25000000000000 : ℝ)^3461 := by
    have hnat : (80813643 : ℕ)^4485*25000000000000^3461 ≤ 7726043283633^3461*200000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80813643 200000000 7726043283633 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278247729/10000000000 : ℝ), (4527903633/10000000000 : ℝ), (80813643/200000000 : ℝ)] ![(33278920133847/100000000000000 : ℝ), (35816906727807/100000000000000 : ℝ), (7726043283633/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278247729/10000000000 : ℝ)|^4485 ≤ (33278920133847/100000000000000 : ℝ)^3461
        have hw : |(4278247729/10000000000 : ℝ)|=(4278247729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4527903633/10000000000 : ℝ)|^4485 ≤ (35816906727807/100000000000000 : ℝ)^3461
        have hw : |(4527903633/10000000000 : ℝ)|=(4527903633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80813643/200000000 : ℝ)|^4485 ≤ (7726043283633/25000000000000 : ℝ)^3461
        have hw : |(80813643/200000000 : ℝ)|=(80813643/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1494_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15563/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5417/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15563/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15563/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15563/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15563/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15563/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15563/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10767/100000 : ℝ) ^ (4483/1024 : ℝ) ≤ (578866890084487/10000000000000000000 : ℝ) := by
    have hpowers : (10767/100000 : ℝ)^4483 ≤ (578866890084487/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10767 : ℕ)^4483*10000000000000000000^1024 ≤ 578866890084487^1024*100000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10767 100000 578866890084487 10000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10767/100000 : ℝ)) (X := (578866890084487/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15563/100000 : ℝ) ^ (4483/1024 : ℝ) ≤ (14521495817046373/50000000000000000000 : ℝ) := by
    have hpowers : (15563/100000 : ℝ)^4483 ≤ (14521495817046373/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15563 : ℕ)^4483*50000000000000000000^1024 ≤ 14521495817046373^1024*100000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15563 100000 14521495817046373 50000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15563/100000 : ℝ)) (X := (14521495817046373/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000578866890084487/5000000000000000000 : ℝ) ≤ (5000132217983953/5000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (5000578866890084487/5000000000000000000 : ℝ)^1024 ≤ (5000132217983953/5000000000000000 : ℝ)^4483 := by
      have hnat : (5000578866890084487 : ℕ)^1024*5000000000000000^4483 ≤ 5000132217983953^4483*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000578866890084487 5000000000000000000 5000132217983953 5000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000132217983953/5000000000000000 : ℝ)) (X := (5000578866890084487/5000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252176978783433601/6250000000000000000 : ℝ) ≤ (5000397756284339/5000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (6252176978783433601/6250000000000000000 : ℝ)^1024 ≤ (5000397756284339/5000000000000000 : ℝ)^4483 := by
      have hnat : (6252176978783433601 : ℕ)^1024*5000000000000000^4483 ≤ 5000397756284339^4483*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252176978783433601 6250000000000000000 5000397756284339 5000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000397756284339/5000000000000000 : ℝ)) (X := (6252176978783433601/6250000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014521495817046373/25000000000000000000 : ℝ) ≤ (200026531783389/200000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (25014521495817046373/25000000000000000000 : ℝ)^1024 ≤ (200026531783389/200000000000000 : ℝ)^4483 := by
      have hnat : (25014521495817046373 : ℕ)^1024*200000000000000^4483 ≤ 200026531783389^4483*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014521495817046373 25000000000000000000 200026531783389 200000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200026531783389/200000000000000 : ℝ)) (X := (25014521495817046373/25000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(578866890084487/10000000000000000000 : ℝ) ≤ ((93652015686291119/93671875000000000 : ℝ)+2*(132769150193/119900000000000 : ℝ)*(10767/100000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (93652015686291119/93671875000000000 : ℝ)+2*(132769150193/119900000000000 : ℝ)*(10767/100000 : ℝ)=(5000132217983953/5000000000000000 : ℝ) by norm_num, show 1+2*(578866890084487/10000000000000000000 : ℝ)=(5000578866890084487/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14521495817046373/50000000000000000000 : ℝ)+(578866890084487/10000000000000000000 : ℝ) ≤ ((93652015686291119/93671875000000000 : ℝ)+(132769150193/119900000000000 : ℝ)*((15563/100000 : ℝ)+(10767/100000 : ℝ)))^(4483/1024 : ℝ) := by
    rw [show (93652015686291119/93671875000000000 : ℝ)+(132769150193/119900000000000 : ℝ)*((15563/100000 : ℝ)+(10767/100000 : ℝ))=(5000397756284339/5000000000000000 : ℝ) by norm_num, show 1+(14521495817046373/50000000000000000000 : ℝ)+(578866890084487/10000000000000000000 : ℝ)=(6252176978783433601/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14521495817046373/50000000000000000000 : ℝ) ≤ ((93652015686291119/93671875000000000 : ℝ)+2*(132769150193/119900000000000 : ℝ)*(15563/100000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (93652015686291119/93671875000000000 : ℝ)+2*(132769150193/119900000000000 : ℝ)*(15563/100000 : ℝ)=(200026531783389/200000000000000 : ℝ) by norm_num, show 1+2*(14521495817046373/50000000000000000000 : ℝ)=(25014521495817046373/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (93652015686291119/93671875000000000 : ℝ)*(X 1 0+X 2 0)+(132769150193/119900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (10767/100000 : ℝ)) (hi := (15563/100000 : ℝ)) (c := (93652015686291119/93671875000000000 : ℝ)) (alpha := (132769150193/119900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (93652015686291119/93671875000000000 : ℝ)*(X 0 1+X 2 1)+(132769150193/119900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (10767/100000 : ℝ)) (hi := (15563/100000 : ℝ)) (c := (93652015686291119/93671875000000000 : ℝ)) (alpha := (132769150193/119900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (93652015686291119/93671875000000000 : ℝ)*(X 0 2+X 1 2)+(132769150193/119900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (10767/100000 : ℝ)) (hi := (15563/100000 : ℝ)) (c := (93652015686291119/93671875000000000 : ℝ)) (alpha := (132769150193/119900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-473715019/2500000000 : ℝ)*X 0 0+(543610431/1000000000 : ℝ)*X 0 1+(5216207981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((26763541/50000000 : ℝ)*X 1 0+(-2007533629/10000000000 : ℝ)*X 1 1+(5216208657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334544273/625000000 : ℝ)*X 2 0+(1304051981/2500000000 : ℝ)*X 2 1+(-1003767189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4278179347/10000000000 : ℝ)*X 0 0+(807625649/2000000000 : ℝ)*X 0 1+(1132609937/2500000000 : ℝ)*X 0 2+(4278179347/10000000000 : ℝ)*X 1 0+(807625649/2000000000 : ℝ)*X 1 1+(1132609937/2500000000 : ℝ)*X 1 2+(4278179347/10000000000 : ℝ)*X 2 0+(807625649/2000000000 : ℝ)*X 2 1+(1132609937/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1894890979/10000000000 : ℝ)*X 0 0+(5217341241/10000000000 : ℝ)*X 0 1+(1086992423/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323786291/2500000000 : ℝ)*X 1 0+(-894390257/5000000000 : ℝ)*X 1 1+(5434962003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295145307/10000000000 : ℝ)*X 2 0+(543496173/1000000000 : ℝ)*X 2 1+(-223597587/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4278247729/10000000000 : ℝ)*X 0 0+(4527903633/10000000000 : ℝ)*X 0 1+(80813643/200000000 : ℝ)*X 0 2+(4278247729/10000000000 : ℝ)*X 1 0+(4527903633/10000000000 : ℝ)*X 1 1+(80813643/200000000 : ℝ)*X 1 2+(4278247729/10000000000 : ℝ)*X 2 0+(4527903633/10000000000 : ℝ)*X 2 1+(80813643/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4065506343119703668920041/340625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66828961/4000000000000 : ℝ)*(base19) + (1881842453/100000000000000 : ℝ)*(base23) + (119830977/100000000000000 : ℝ)*(upper3) + (94439679/100000000000000 : ℝ)*(lower4) + (164473799301377/5000000000000 : ℝ)*(major0) + (164473799301377/5000000000000 : ℝ)*(major1) + (164473799301377/5000000000000 : ℝ)*(major2) + (4547647040923947/100000000000000 : ℝ)*(sp0) + (4547690481691407/100000000000000 : ℝ)*(sp1) + (56846002790897/1250000000000 : ℝ)*(sp2) + (253905795220707/12500000000000 : ℝ)*(sp3) + (9022298297/20000000000000 : ℝ)*(sp4) + (10047301219/100000000000000 : ℝ)*(sp6) + (13060026271/100000000000000 : ℝ)*(sp7) + (253907427723991/12500000000000 : ℝ)*(f.failure) + (568461519051929/12500000000000 : ℝ)*(f.sum) + (76715747489/37468750000000000000000000 : ℝ)*base65 + (534040982789613/468359375000000000000000000000 : ℝ)*base67 + (943258496963423/1873437500000000000000000000000 : ℝ)*base70 + (31691614875670029/3746875000000000000000000000000 : ℝ)*base71 + (352825327663/149875000000000000000000000 : ℝ)*base73 + (1409239438001279/3746875000000000000000000000000 : ℝ)*base75 + (12520681600199077/1873437500000000000000000000000 : ℝ)*base77 + (19651583873136221/3746875000000000000000000000000 : ℝ)*base80 + (730656962939/599500000000000000000000000 : ℝ)*base81 + (4141931/625000000000000000000 : ℝ)*base89 + (4141931/625000000000000000000 : ℝ)*base91 + (4141931/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7959687644076533058947307/749375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2333382683/100000000000000 : ℝ)*(base19) + (2600082043/100000000000000 : ℝ)*(base23) + (78890113/100000000000000 : ℝ)*(upper2) + (164136611/50000000000000 : ℝ)*(upper3) + (37152901/12500000000000 : ℝ)*(upper5) + (66476007545439/2000000000000 : ℝ)*(major0) + (66476007545439/2000000000000 : ℝ)*(major1) + (66476007545439/2000000000000 : ℝ)*(major2) + (1566739939/5000000000000 : ℝ)*(sp1) + (6149538871/20000000000000 : ℝ)*(sp2) + (1148786395904589/25000000000000 : ℝ)*(sp4) + (4595111915436893/100000000000000 : ℝ)*(sp5) + (2297556117920979/50000000000000 : ℝ)*(sp6) + (1026227408433297/50000000000000 : ℝ)*(sp7) + (1026227408433297/50000000000000 : ℝ)*(f.failure) + (1148786395904589/25000000000000 : ℝ)*(f.sum) + (225890237657/299750000000000000000000000 : ℝ)*base66 + (197287409145589/749375000000000000000000000000 : ℝ)*base67 + (6924108867796839/749375000000000000000000000000 : ℝ)*base69 + (9566917362070589/749375000000000000000000000000 : ℝ)*base71 + (213326111967/23980000000000000000000000 : ℝ)*base74 + (1697339181835607/374687500000000000000000000000 : ℝ)*base75 + (5190475718004339/749375000000000000000000000000 : ℝ)*base77 + (1733040066001911/749375000000000000000000000000 : ℝ)*base80 + (997820061253/299750000000000000000000000 : ℝ)*base81 + (17141277/2500000000000000000000 : ℝ)*base89 + (17141277/2500000000000000000000 : ℝ)*base91 + (17141277/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1494_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15563/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5417/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1494_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1494_s5_0 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-473732811/2500000000 : ℝ)*x 0 + (271782351/500000000 : ℝ)*x 1 + (5216618137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473732811/2500000000 : ℝ)^4485 ≤ (11583940004203/100000000000000 : ℝ)^3461 := by
    have hnat : (473732811 : ℕ)^4485*100000000000000^3461 ≤ 11583940004203^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473732811 2500000000 11583940004203 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271782351/500000000 : ℝ)^4485 ≤ (45385852509389/100000000000000 : ℝ)^3461 := by
    have hnat : (271782351 : ℕ)^4485*100000000000000^3461 ≤ 45385852509389^3461*500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271782351 500000000 45385852509389 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216618137/10000000000 : ℝ)^4485 ≤ (21515103731517/50000000000000 : ℝ)^3461 := by
    have hnat : (5216618137 : ℕ)^4485*50000000000000^3461 ≤ 21515103731517^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216618137 10000000000 21515103731517 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473732811/2500000000 : ℝ), (271782351/500000000 : ℝ), (5216618137/10000000000 : ℝ)] ![(11583940004203/100000000000000 : ℝ), (45385852509389/100000000000000 : ℝ), (21515103731517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473732811/2500000000 : ℝ)|^4485 ≤ (11583940004203/100000000000000 : ℝ)^3461
        have hw : |(-473732811/2500000000 : ℝ)|=(473732811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271782351/500000000 : ℝ)|^4485 ≤ (45385852509389/100000000000000 : ℝ)^3461
        have hw : |(271782351/500000000 : ℝ)|=(271782351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216618137/10000000000 : ℝ)|^4485 ≤ (21515103731517/50000000000000 : ℝ)^3461
        have hw : |(5216618137/10000000000 : ℝ)|=(5216618137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s5_1 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669073603/1250000000 : ℝ)*x 0 + (-2007149421/10000000000 : ℝ)*x 1 + (1043323717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669073603/1250000000 : ℝ)^4485 ≤ (44489195767883/100000000000000 : ℝ)^3461 := by
    have hnat : (669073603 : ℕ)^4485*100000000000000^3461 ≤ 44489195767883^3461*1250000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669073603 1250000000 44489195767883 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007149421/10000000000 : ℝ)^4485 ≤ (12480591965173/100000000000000 : ℝ)^3461 := by
    have hnat : (2007149421 : ℕ)^4485*100000000000000^3461 ≤ 12480591965173^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007149421 10000000000 12480591965173 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043323717/2000000000 : ℝ)^4485 ≤ (10757553062949/25000000000000 : ℝ)^3461 := by
    have hnat : (1043323717 : ℕ)^4485*25000000000000^3461 ≤ 10757553062949^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043323717 2000000000 10757553062949 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669073603/1250000000 : ℝ), (-2007149421/10000000000 : ℝ), (1043323717/2000000000 : ℝ)] ![(44489195767883/100000000000000 : ℝ), (12480591965173/100000000000000 : ℝ), (10757553062949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669073603/1250000000 : ℝ)|^4485 ≤ (44489195767883/100000000000000 : ℝ)^3461
        have hw : |(669073603/1250000000 : ℝ)|=(669073603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2007149421/10000000000 : ℝ)|^4485 ≤ (12480591965173/100000000000000 : ℝ)^3461
        have hw : |(-2007149421/10000000000 : ℝ)|=(2007149421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043323717/2000000000 : ℝ)|^4485 ≤ (10757553062949/25000000000000 : ℝ)^3461
        have hw : |(1043323717/2000000000 : ℝ)|=(1043323717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s5_2 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676294181/5000000000 : ℝ)*x 0 + (41732953/80000000 : ℝ)*x 1 + (-2007149323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676294181/5000000000 : ℝ)^4485 ≤ (44489190791733/100000000000000 : ℝ)^3461 := by
    have hnat : (2676294181 : ℕ)^4485*100000000000000^3461 ≤ 44489190791733^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676294181 5000000000 44489190791733 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41732953/80000000 : ℝ)^4485 ≤ (8606043604793/20000000000000 : ℝ)^3461 := by
    have hnat : (41732953 : ℕ)^4485*20000000000000^3461 ≤ 8606043604793^3461*80000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41732953 80000000 8606043604793 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007149323/10000000000 : ℝ)^4485 ≤ (12480591175509/100000000000000 : ℝ)^3461 := by
    have hnat : (2007149323 : ℕ)^4485*100000000000000^3461 ≤ 12480591175509^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007149323 10000000000 12480591175509 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676294181/5000000000 : ℝ), (41732953/80000000 : ℝ), (-2007149323/10000000000 : ℝ)] ![(44489190791733/100000000000000 : ℝ), (8606043604793/20000000000000 : ℝ), (12480591175509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676294181/5000000000 : ℝ)|^4485 ≤ (44489190791733/100000000000000 : ℝ)^3461
        have hw : |(2676294181/5000000000 : ℝ)|=(2676294181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41732953/80000000 : ℝ)|^4485 ≤ (8606043604793/20000000000000 : ℝ)^3461
        have hw : |(41732953/80000000 : ℝ)|=(41732953/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2007149323/10000000000 : ℝ)|^4485 ≤ (12480591175509/100000000000000 : ℝ)^3461
        have hw : |(-2007149323/10000000000 : ℝ)|=(2007149323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s5_3 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855644607/2000000000 : ℝ)*x 0 + (4039093461/10000000000 : ℝ)*x 1 + (2264731907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855644607/2000000000 : ℝ)^4485 ≤ (33278671216469/100000000000000 : ℝ)^3461 := by
    have hnat : (855644607 : ℕ)^4485*100000000000000^3461 ≤ 33278671216469^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855644607 2000000000 33278671216469 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4039093461/10000000000 : ℝ)^4485 ≤ (6177685668617/20000000000000 : ℝ)^3461 := by
    have hnat : (4039093461 : ℕ)^4485*20000000000000^3461 ≤ 6177685668617^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039093461 10000000000 6177685668617 20000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264731907/5000000000 : ℝ)^4485 ≤ (35832900424981/100000000000000 : ℝ)^3461 := by
    have hnat : (2264731907 : ℕ)^4485*100000000000000^3461 ≤ 35832900424981^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264731907 5000000000 35832900424981 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855644607/2000000000 : ℝ), (4039093461/10000000000 : ℝ), (2264731907/5000000000 : ℝ)] ![(33278671216469/100000000000000 : ℝ), (6177685668617/20000000000000 : ℝ), (35832900424981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855644607/2000000000 : ℝ)|^4485 ≤ (33278671216469/100000000000000 : ℝ)^3461
        have hw : |(855644607/2000000000 : ℝ)|=(855644607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4039093461/10000000000 : ℝ)|^4485 ≤ (6177685668617/20000000000000 : ℝ)^3461
        have hw : |(4039093461/10000000000 : ℝ)|=(4039093461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2264731907/5000000000 : ℝ)|^4485 ≤ (35832900424981/100000000000000 : ℝ)^3461
        have hw : |(2264731907/5000000000 : ℝ)|=(2264731907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s5_4 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-378992147/2000000000 : ℝ)*x 0 + (5217742917/10000000000 : ℝ)*x 1 + (5434514183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (378992147/2000000000 : ℝ)^4485 ≤ (5792086813223/50000000000000 : ℝ)^3461 := by
    have hnat : (378992147 : ℕ)^4485*50000000000000^3461 ≤ 5792086813223^3461*2000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378992147 2000000000 5792086813223 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217742917/10000000000 : ℝ)^4485 ≤ (43042230845939/100000000000000 : ℝ)^3461 := by
    have hnat : (5217742917 : ℕ)^4485*100000000000000^3461 ≤ 43042230845939^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217742917 10000000000 43042230845939 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434514183/10000000000 : ℝ)^4485 ≤ (45373595510873/100000000000000 : ℝ)^3461 := by
    have hnat : (5434514183 : ℕ)^4485*100000000000000^3461 ≤ 45373595510873^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434514183 10000000000 45373595510873 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-378992147/2000000000 : ℝ), (5217742917/10000000000 : ℝ), (5434514183/10000000000 : ℝ)] ![(5792086813223/50000000000000 : ℝ), (43042230845939/100000000000000 : ℝ), (45373595510873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-378992147/2000000000 : ℝ)|^4485 ≤ (5792086813223/50000000000000 : ℝ)^3461
        have hw : |(-378992147/2000000000 : ℝ)|=(378992147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217742917/10000000000 : ℝ)|^4485 ≤ (43042230845939/100000000000000 : ℝ)^3461
        have hw : |(5217742917/10000000000 : ℝ)|=(5217742917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434514183/10000000000 : ℝ)|^4485 ≤ (45373595510873/100000000000000 : ℝ)^3461
        have hw : |(5434514183/10000000000 : ℝ)|=(5434514183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s5_5 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647626441/5000000000 : ℝ)*x 0 + (-894627067/5000000000 : ℝ)*x 1 + (543451419/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647626441/5000000000 : ℝ)^4485 ≤ (10968154456481/25000000000000 : ℝ)^3461 := by
    have hnat : (2647626441 : ℕ)^4485*25000000000000^3461 ≤ 10968154456481^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647626441 5000000000 10968154456481 25000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894627067/5000000000 : ℝ)^4485 ≤ (5376893291227/50000000000000 : ℝ)^3461 := by
    have hnat : (894627067 : ℕ)^4485*50000000000000^3461 ≤ 5376893291227^3461*5000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894627067 5000000000 5376893291227 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543451419/1000000000 : ℝ)^4485 ≤ (45373595586609/100000000000000 : ℝ)^3461 := by
    have hnat : (543451419 : ℕ)^4485*100000000000000^3461 ≤ 45373595586609^3461*1000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543451419 1000000000 45373595586609 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647626441/5000000000 : ℝ), (-894627067/5000000000 : ℝ), (543451419/1000000000 : ℝ)] ![(10968154456481/25000000000000 : ℝ), (5376893291227/50000000000000 : ℝ), (45373595586609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647626441/5000000000 : ℝ)|^4485 ≤ (10968154456481/25000000000000 : ℝ)^3461
        have hw : |(2647626441/5000000000 : ℝ)|=(2647626441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-894627067/5000000000 : ℝ)|^4485 ≤ (5376893291227/50000000000000 : ℝ)^3461
        have hw : |(-894627067/5000000000 : ℝ)|=(894627067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543451419/1000000000 : ℝ)|^4485 ≤ (45373595586609/100000000000000 : ℝ)^3461
        have hw : |(543451419/1000000000 : ℝ)|=(543451419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s5_6 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323813221/2500000000 : ℝ)*x 0 + (5434514189/10000000000 : ℝ)*x 1 + (-447313533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323813221/2500000000 : ℝ)^4485 ≤ (43872617847397/100000000000000 : ℝ)^3461 := by
    have hnat : (1323813221 : ℕ)^4485*100000000000000^3461 ≤ 43872617847397^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323813221 2500000000 43872617847397 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434514189/10000000000 : ℝ)^4485 ≤ (45373595575789/100000000000000 : ℝ)^3461 := by
    have hnat : (5434514189 : ℕ)^4485*100000000000000^3461 ≤ 45373595575789^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434514189 10000000000 45373595575789 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447313533/2500000000 : ℝ)^4485 ≤ (5376893283439/50000000000000 : ℝ)^3461 := by
    have hnat : (447313533 : ℕ)^4485*50000000000000^3461 ≤ 5376893283439^3461*2500000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447313533 2500000000 5376893283439 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323813221/2500000000 : ℝ), (5434514189/10000000000 : ℝ), (-447313533/2500000000 : ℝ)] ![(43872617847397/100000000000000 : ℝ), (45373595575789/100000000000000 : ℝ), (5376893283439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323813221/2500000000 : ℝ)|^4485 ≤ (43872617847397/100000000000000 : ℝ)^3461
        have hw : |(1323813221/2500000000 : ℝ)|=(1323813221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434514189/10000000000 : ℝ)|^4485 ≤ (45373595575789/100000000000000 : ℝ)^3461
        have hw : |(5434514189/10000000000 : ℝ)|=(5434514189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447313533/2500000000 : ℝ)|^4485 ≤ (5376893283439/50000000000000 : ℝ)^3461
        have hw : |(-447313533/2500000000 : ℝ)|=(447313533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1494_s5_7 (p : ℝ) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278289841/10000000000 : ℝ)*x 0 + (4526947399/10000000000 : ℝ)*x 1 + (4041628247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278289841/10000000000 : ℝ)^4485 ≤ (33279344626957/100000000000000 : ℝ)^3461 := by
    have hnat : (4278289841 : ℕ)^4485*100000000000000^3461 ≤ 33279344626957^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278289841 10000000000 33279344626957 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526947399/10000000000 : ℝ)^4485 ≤ (17903552503123/50000000000000 : ℝ)^3461 := by
    have hnat : (4526947399 : ℕ)^4485*50000000000000^3461 ≤ 17903552503123^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526947399 10000000000 17903552503123 50000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4041628247/10000000000 : ℝ)^4485 ≤ (30913550352141/100000000000000 : ℝ)^3461 := by
    have hnat : (4041628247 : ℕ)^4485*100000000000000^3461 ≤ 30913550352141^3461*10000000000^4485 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041628247 10000000000 30913550352141 100000000000000 4485 3461 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4485/1024 : ℝ)) 4485 3461 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278289841/10000000000 : ℝ), (4526947399/10000000000 : ℝ), (4041628247/10000000000 : ℝ)] ![(33279344626957/100000000000000 : ℝ), (17903552503123/50000000000000 : ℝ), (30913550352141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278289841/10000000000 : ℝ)|^4485 ≤ (33279344626957/100000000000000 : ℝ)^3461
        have hw : |(4278289841/10000000000 : ℝ)|=(4278289841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526947399/10000000000 : ℝ)|^4485 ≤ (17903552503123/50000000000000 : ℝ)^3461
        have hw : |(4526947399/10000000000 : ℝ)|=(4526947399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4041628247/10000000000 : ℝ)|^4485 ≤ (30913550352141/100000000000000 : ℝ)^3461
        have hw : |(4041628247/10000000000 : ℝ)|=(4041628247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1494_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5417/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10843/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5417/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5417/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5417/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5417/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5417/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5417/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5417/50000 : ℝ) ^ (4483/1024 : ℝ) ≤ (5948033003872531/100000000000000000000 : ℝ) := by
    have hpowers : (5417/50000 : ℝ)^4483 ≤ (5948033003872531/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5417 : ℕ)^4483*100000000000000000000^1024 ≤ 5948033003872531^1024*50000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5417 50000 5948033003872531 100000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5417/50000 : ℝ)) (X := (5948033003872531/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4483/1024 : ℝ) ≤ (569025923276449/2000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4483 ≤ (569025923276449/2000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4483*2000000000000000000^1024 ≤ 569025923276449^1024*10000^4483 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 569025923276449 2000000000000000000 4483 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (569025923276449/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005948033003872531/50000000000000000000 : ℝ) ≤ (1000027171564959/1000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (50005948033003872531/50000000000000000000 : ℝ)^1024 ≤ (1000027171564959/1000000000000000 : ℝ)^4483 := by
      have hnat : (50005948033003872531 : ℕ)^1024*1000000000000000^4483 ≤ 1000027171564959^4483*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005948033003872531 50000000000000000000 1000027171564959 1000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000027171564959/1000000000000000 : ℝ)) (X := (50005948033003872531/50000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034399329167694981/100000000000000000000 : ℝ) ≤ (10000785639958483/10000000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (100034399329167694981/100000000000000000000 : ℝ)^1024 ≤ (10000785639958483/10000000000000000 : ℝ)^4483 := by
      have hnat : (100034399329167694981 : ℕ)^1024*10000000000000000^4483 ≤ 10000785639958483^4483*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034399329167694981 100000000000000000000 10000785639958483 10000000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000785639958483/10000000000000000 : ℝ)) (X := (100034399329167694981/100000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000569025923276449/1000000000000000000 : ℝ) ≤ (625081222766711/625000000000000 : ℝ) ^ (4483/1024 : ℝ) := by
    have hpowers : (1000569025923276449/1000000000000000000 : ℝ)^1024 ≤ (625081222766711/625000000000000 : ℝ)^4483 := by
      have hnat : (1000569025923276449 : ℕ)^1024*625000000000000^4483 ≤ 625081222766711^4483*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000569025923276449 1000000000000000000 625081222766711 625000000000000 1024 4483 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625081222766711/625000000000000 : ℝ)) (X := (1000569025923276449/1000000000000000000 : ℝ)) (by norm_num) 4483 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5948033003872531/100000000000000000000 : ℝ) ≤ ((11637532349034849379/11640000000000000000 : ℝ)+2*(513924308893/465600000000000 : ℝ)*(5417/50000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (11637532349034849379/11640000000000000000 : ℝ)+2*(513924308893/465600000000000 : ℝ)*(5417/50000 : ℝ)=(1000027171564959/1000000000000000 : ℝ) by norm_num, show 1+2*(5948033003872531/100000000000000000000 : ℝ)=(50005948033003872531/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(569025923276449/2000000000000000000 : ℝ)+(5948033003872531/100000000000000000000 : ℝ) ≤ ((11637532349034849379/11640000000000000000 : ℝ)+(513924308893/465600000000000 : ℝ)*((1549/10000 : ℝ)+(5417/50000 : ℝ)))^(4483/1024 : ℝ) := by
    rw [show (11637532349034849379/11640000000000000000 : ℝ)+(513924308893/465600000000000 : ℝ)*((1549/10000 : ℝ)+(5417/50000 : ℝ))=(10000785639958483/10000000000000000 : ℝ) by norm_num, show 1+(569025923276449/2000000000000000000 : ℝ)+(5948033003872531/100000000000000000000 : ℝ)=(100034399329167694981/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(569025923276449/2000000000000000000 : ℝ) ≤ ((11637532349034849379/11640000000000000000 : ℝ)+2*(513924308893/465600000000000 : ℝ)*(1549/10000 : ℝ))^(4483/1024 : ℝ) := by
    rw [show (11637532349034849379/11640000000000000000 : ℝ)+2*(513924308893/465600000000000 : ℝ)*(1549/10000 : ℝ)=(625081222766711/625000000000000 : ℝ) by norm_num, show 1+2*(569025923276449/2000000000000000000 : ℝ)=(1000569025923276449/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11637532349034849379/11640000000000000000 : ℝ)*(X 1 0+X 2 0)+(513924308893/465600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (5417/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11637532349034849379/11640000000000000000 : ℝ)) (alpha := (513924308893/465600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11637532349034849379/11640000000000000000 : ℝ)*(X 0 1+X 2 1)+(513924308893/465600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (5417/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11637532349034849379/11640000000000000000 : ℝ)) (alpha := (513924308893/465600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11637532349034849379/11640000000000000000 : ℝ)*(X 0 2+X 1 2)+(513924308893/465600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4483/1024 : ℝ)) (lo := (5417/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11637532349034849379/11640000000000000000 : ℝ)) (alpha := (513924308893/465600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-473732811/2500000000 : ℝ)*X 0 0+(271782351/500000000 : ℝ)*X 0 1+(5216618137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669073603/1250000000 : ℝ)*X 1 0+(-2007149421/10000000000 : ℝ)*X 1 1+(1043323717/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676294181/5000000000 : ℝ)*X 2 0+(41732953/80000000 : ℝ)*X 2 1+(-2007149323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((855644607/2000000000 : ℝ)*X 0 0+(4039093461/10000000000 : ℝ)*X 0 1+(2264731907/5000000000 : ℝ)*X 0 2+(855644607/2000000000 : ℝ)*X 1 0+(4039093461/10000000000 : ℝ)*X 1 1+(2264731907/5000000000 : ℝ)*X 1 2+(855644607/2000000000 : ℝ)*X 2 0+(4039093461/10000000000 : ℝ)*X 2 1+(2264731907/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-378992147/2000000000 : ℝ)*X 0 0+(5217742917/10000000000 : ℝ)*X 0 1+(5434514183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647626441/5000000000 : ℝ)*X 1 0+(-894627067/5000000000 : ℝ)*X 1 1+(543451419/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323813221/2500000000 : ℝ)*X 2 0+(5434514189/10000000000 : ℝ)*X 2 1+(-447313533/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4278289841/10000000000 : ℝ)*X 0 0+(4526947399/10000000000 : ℝ)*X 0 1+(4041628247/10000000000 : ℝ)*X 0 2+(4278289841/10000000000 : ℝ)*X 1 0+(4526947399/10000000000 : ℝ)*X 1 1+(4041628247/10000000000 : ℝ)*X 1 2+(4278289841/10000000000 : ℝ)*X 2 0+(4526947399/10000000000 : ℝ)*X 2 1+(4041628247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1494_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (395748101161053288499871817/48500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1057547149/50000000000000 : ℝ)*(base19) + (1512881069/100000000000000 : ℝ)*(base23) + (281538111/100000000000000 : ℝ)*(upper3) + (55702429/50000000000000 : ℝ)*(upper4) + (162751249/100000000000000 : ℝ)*(upper5) + (825624790768641/25000000000000 : ℝ)*(major0) + (825624790768641/25000000000000 : ℝ)*(major1) + (825624790768641/25000000000000 : ℝ)*(major2) + (2282826945319477/50000000000000 : ℝ)*(sp0) + (142677958555329/3125000000000 : ℝ)*(sp1) + (4565695275983757/100000000000000 : ℝ)*(sp2) + (1019643812900009/50000000000000 : ℝ)*(sp3) + (2681139117/6250000000000 : ℝ)*(sp4) + (6819746227/50000000000000 : ℝ)*(sp7) + (254912658161559/12500000000000 : ℝ)*(f.failure) + (2282848394432413/50000000000000 : ℝ)*(f.sum) + (12804844030351/1940000000000000000000000000 : ℝ)*base65 + (1515612773795383687/97000000000000000000000000000000 : ℝ)*base68 + (1187837446647383687/97000000000000000000000000000000 : ℝ)*base70 + (554796575491383687/97000000000000000000000000000000 : ℝ)*base72 + (4179245661169/1940000000000000000000000000 : ℝ)*base74 + (2110638372429383687/97000000000000000000000000000000 : ℝ)*base76 + (720264700805383687/97000000000000000000000000000000 : ℝ)*base78 + (376385305132383687/97000000000000000000000000000000 : ℝ)*base80 + (1053721599789/1940000000000000000000000000 : ℝ)*base82 + (1880619/625000000000000000000 : ℝ)*base89 + (1880619/625000000000000000000 : ℝ)*base91 + (1880619/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11072748476841107336981703/1552000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146482617/12500000000000 : ℝ)*(base19) + (1265859763/100000000000000 : ℝ)*(base23) + (37296697/25000000000000 : ℝ)*(upper3) + (10293523/25000000000000 : ℝ)*(lower4) + (146075527/100000000000000 : ℝ)*(upper5) + (26694626468957/800000000000 : ℝ)*(major0) + (26694626468957/800000000000 : ℝ)*(major1) + (26694626468957/800000000000 : ℝ)*(major2) + (8927529073/50000000000000 : ℝ)*(sp1) + (1199646523/6250000000000 : ℝ)*(sp2) + (4613156783263131/100000000000000 : ℝ)*(sp4) + (4613137756344049/100000000000000 : ℝ)*(sp5) + (4613136323059/100000000000 : ℝ)*(sp6) + (2060499596159353/100000000000000 : ℝ)*(sp7) + (2060499596159353/100000000000000 : ℝ)*(f.failure) + (4613156783263131/100000000000000 : ℝ)*(f.sum) + (5308002251297/4656000000000000000000000000 : ℝ)*base65 + (43872802470635297/9312000000000000000000000000000 : ℝ)*base68 + (57142078319915297/9312000000000000000000000000000 : ℝ)*base70 + (38126561097012703/9312000000000000000000000000000 : ℝ)*base71 + (3826472493923/931200000000000000000000000 : ℝ)*base74 + (11059893307979297/9312000000000000000000000000000 : ℝ)*base76 + (15511049642484703/9312000000000000000000000000000 : ℝ)*base77 + (38346092040011297/9312000000000000000000000000000 : ℝ)*base80 + (10379559765487/4656000000000000000000000000 : ℝ)*base82 + (12102373/5000000000000000000000 : ℝ)*base89 + (12102373/5000000000000000000000 : ℝ)*base91 + (12102373/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1494_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5417/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1494_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1494_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1494_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1494_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1494_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4483/1024 : ℝ) ≤ p) (hpb : p ≤ (4485/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80971341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1494_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

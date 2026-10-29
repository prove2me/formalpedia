-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1510_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:59.065577+00:00
-- url     : https://prove2.me/submissions/c6678581-0bf8-4fa8-9a36-3dd9280ff802

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
theorem support_rectangle_w1510_s0_0 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1687957253/10000000000 : ℝ)*x 0 + (5914369989/10000000000 : ℝ)*x 1 + (970892157/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1687957253/10000000000 : ℝ)^4517 ≤ (2504935090861/25000000000000 : ℝ)^3493 := by
    have hnat : (1687957253 : ℕ)^4517*25000000000000^3493 ≤ 2504935090861^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687957253 10000000000 2504935090861 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5914369989/10000000000 : ℝ)^4517 ≤ (50703938702059/100000000000000 : ℝ)^3493 := by
    have hnat : (5914369989 : ℕ)^4517*100000000000000^3493 ≤ 50703938702059^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5914369989 10000000000 50703938702059 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970892157/2000000000 : ℝ)^4517 ≤ (19638160460151/50000000000000 : ℝ)^3493 := by
    have hnat : (970892157 : ℕ)^4517*50000000000000^3493 ≤ 19638160460151^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970892157 2000000000 19638160460151 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1687957253/10000000000 : ℝ), (5914369989/10000000000 : ℝ), (970892157/2000000000 : ℝ)] ![(2504935090861/25000000000000 : ℝ), (50703938702059/100000000000000 : ℝ), (19638160460151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1687957253/10000000000 : ℝ)|^4517 ≤ (2504935090861/25000000000000 : ℝ)^3493
        have hw : |(-1687957253/10000000000 : ℝ)|=(1687957253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5914369989/10000000000 : ℝ)|^4517 ≤ (50703938702059/100000000000000 : ℝ)^3493
        have hw : |(5914369989/10000000000 : ℝ)|=(5914369989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(970892157/2000000000 : ℝ)|^4517 ≤ (19638160460151/50000000000000 : ℝ)^3493
        have hw : |(970892157/2000000000 : ℝ)|=(970892157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s0_1 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2739207737/5000000000 : ℝ)*x 0 + (-285276217/1250000000 : ℝ)*x 1 + (4854460719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2739207737/5000000000 : ℝ)^4517 ≤ (22961996631621/50000000000000 : ℝ)^3493 := by
    have hnat : (2739207737 : ℕ)^4517*50000000000000^3493 ≤ 22961996631621^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739207737 5000000000 22961996631621 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285276217/1250000000 : ℝ)^4517 ≤ (14799686483703/100000000000000 : ℝ)^3493 := by
    have hnat : (285276217 : ℕ)^4517*100000000000000^3493 ≤ 14799686483703^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285276217 1250000000 14799686483703 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4854460719/10000000000 : ℝ)^4517 ≤ (4909540028721/12500000000000 : ℝ)^3493 := by
    have hnat : (4854460719 : ℕ)^4517*12500000000000^3493 ≤ 4909540028721^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4854460719 10000000000 4909540028721 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2739207737/5000000000 : ℝ), (-285276217/1250000000 : ℝ), (4854460719/10000000000 : ℝ)] ![(22961996631621/50000000000000 : ℝ), (14799686483703/100000000000000 : ℝ), (4909540028721/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2739207737/5000000000 : ℝ)|^4517 ≤ (22961996631621/50000000000000 : ℝ)^3493
        have hw : |(2739207737/5000000000 : ℝ)|=(2739207737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-285276217/1250000000 : ℝ)|^4517 ≤ (14799686483703/100000000000000 : ℝ)^3493
        have hw : |(-285276217/1250000000 : ℝ)|=(285276217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4854460719/10000000000 : ℝ)|^4517 ≤ (4909540028721/12500000000000 : ℝ)^3493
        have hw : |(4854460719/10000000000 : ℝ)|=(4854460719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s0_2 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2739207763/5000000000 : ℝ)*x 0 + (75850949/156250000 : ℝ)*x 1 + (-2282209649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2739207763/5000000000 : ℝ)^4517 ≤ (45923993826931/100000000000000 : ℝ)^3493 := by
    have hnat : (2739207763 : ℕ)^4517*100000000000000^3493 ≤ 45923993826931^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739207763 5000000000 45923993826931 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75850949/156250000 : ℝ)^4517 ≤ (39276320407633/100000000000000 : ℝ)^3493 := by
    have hnat : (75850949 : ℕ)^4517*100000000000000^3493 ≤ 39276320407633^3493*156250000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75850949 156250000 39276320407633 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2282209649/10000000000 : ℝ)^4517 ≤ (3699921438533/25000000000000 : ℝ)^3493 := by
    have hnat : (2282209649 : ℕ)^4517*25000000000000^3493 ≤ 3699921438533^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282209649 10000000000 3699921438533 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2739207763/5000000000 : ℝ), (75850949/156250000 : ℝ), (-2282209649/10000000000 : ℝ)] ![(45923993826931/100000000000000 : ℝ), (39276320407633/100000000000000 : ℝ), (3699921438533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2739207763/5000000000 : ℝ)|^4517 ≤ (45923993826931/100000000000000 : ℝ)^3493
        have hw : |(2739207763/5000000000 : ℝ)|=(2739207763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(75850949/156250000 : ℝ)|^4517 ≤ (39276320407633/100000000000000 : ℝ)^3493
        have hw : |(75850949/156250000 : ℝ)|=(75850949/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2282209649/10000000000 : ℝ)|^4517 ≤ (3699921438533/25000000000000 : ℝ)^3493
        have hw : |(-2282209649/10000000000 : ℝ)|=(2282209649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s0_3 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2072841723/5000000000 : ℝ)*x 0 + (386406861/1250000000 : ℝ)*x 1 + (5491302757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072841723/5000000000 : ℝ)^4517 ≤ (6405034588491/20000000000000 : ℝ)^3493 := by
    have hnat : (2072841723 : ℕ)^4517*20000000000000^3493 ≤ 6405034588491^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072841723 5000000000 6405034588491 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386406861/1250000000 : ℝ)^4517 ≤ (21911085271351/100000000000000 : ℝ)^3493 := by
    have hnat : (386406861 : ℕ)^4517*100000000000000^3493 ≤ 21911085271351^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386406861 1250000000 21911085271351 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491302757/10000000000 : ℝ)^4517 ≤ (46063741774287/100000000000000 : ℝ)^3493 := by
    have hnat : (5491302757 : ℕ)^4517*100000000000000^3493 ≤ 46063741774287^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491302757 10000000000 46063741774287 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2072841723/5000000000 : ℝ), (386406861/1250000000 : ℝ), (5491302757/10000000000 : ℝ)] ![(6405034588491/20000000000000 : ℝ), (21911085271351/100000000000000 : ℝ), (46063741774287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2072841723/5000000000 : ℝ)|^4517 ≤ (6405034588491/20000000000000 : ℝ)^3493
        have hw : |(2072841723/5000000000 : ℝ)|=(2072841723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386406861/1250000000 : ℝ)|^4517 ≤ (21911085271351/100000000000000 : ℝ)^3493
        have hw : |(386406861/1250000000 : ℝ)|=(386406861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491302757/10000000000 : ℝ)|^4517 ≤ (46063741774287/100000000000000 : ℝ)^3493
        have hw : |(5491302757/10000000000 : ℝ)|=(5491302757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s0_4 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-845747223/5000000000 : ℝ)*x 0 + (1220376621/2500000000 : ℝ)*x 1 + (1471588853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845747223/5000000000 : ℝ)^4517 ≤ (2511725228963/25000000000000 : ℝ)^3493 := by
    have hnat : (845747223 : ℕ)^4517*25000000000000^3493 ≤ 2511725228963^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845747223 5000000000 2511725228963 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220376621/2500000000 : ℝ)^4517 ≤ (19779760564733/50000000000000 : ℝ)^3493 := by
    have hnat : (1220376621 : ℕ)^4517*50000000000000^3493 ≤ 19779760564733^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220376621 2500000000 19779760564733 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1471588853/2500000000 : ℝ)^4517 ≤ (5039357794047/10000000000000 : ℝ)^3493 := by
    have hnat : (1471588853 : ℕ)^4517*10000000000000^3493 ≤ 5039357794047^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471588853 2500000000 5039357794047 10000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-845747223/5000000000 : ℝ), (1220376621/2500000000 : ℝ), (1471588853/2500000000 : ℝ)] ![(2511725228963/25000000000000 : ℝ), (19779760564733/50000000000000 : ℝ), (5039357794047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-845747223/5000000000 : ℝ)|^4517 ≤ (2511725228963/25000000000000 : ℝ)^3493
        have hw : |(-845747223/5000000000 : ℝ)|=(845747223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1220376621/2500000000 : ℝ)|^4517 ≤ (19779760564733/50000000000000 : ℝ)^3493
        have hw : |(1220376621/2500000000 : ℝ)|=(1220376621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1471588853/2500000000 : ℝ)|^4517 ≤ (5039357794047/10000000000000 : ℝ)^3493
        have hw : |(1471588853/2500000000 : ℝ)|=(1471588853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s0_5 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2594422763/5000000000 : ℝ)*x 0 + (-1250315329/10000000000 : ℝ)*x 1 + (588635517/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2594422763/5000000000 : ℝ)^4517 ≤ (21404817411453/50000000000000 : ℝ)^3493 := by
    have hnat : (2594422763 : ℕ)^4517*50000000000000^3493 ≤ 21404817411453^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594422763 5000000000 21404817411453 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250315329/10000000000 : ℝ)^4517 ≤ (424799369101/6250000000000 : ℝ)^3493 := by
    have hnat : (1250315329 : ℕ)^4517*6250000000000^3493 ≤ 424799369101^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250315329 10000000000 424799369101 6250000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (588635517/1000000000 : ℝ)^4517 ≤ (50393575261329/100000000000000 : ℝ)^3493 := by
    have hnat : (588635517 : ℕ)^4517*100000000000000^3493 ≤ 50393575261329^3493*1000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588635517 1000000000 50393575261329 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2594422763/5000000000 : ℝ), (-1250315329/10000000000 : ℝ), (588635517/1000000000 : ℝ)] ![(21404817411453/50000000000000 : ℝ), (424799369101/6250000000000 : ℝ), (50393575261329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2594422763/5000000000 : ℝ)|^4517 ≤ (21404817411453/50000000000000 : ℝ)^3493
        have hw : |(2594422763/5000000000 : ℝ)|=(2594422763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1250315329/10000000000 : ℝ)|^4517 ≤ (424799369101/6250000000000 : ℝ)^3493
        have hw : |(-1250315329/10000000000 : ℝ)|=(1250315329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(588635517/1000000000 : ℝ)|^4517 ≤ (50393575261329/100000000000000 : ℝ)^3493
        have hw : |(588635517/1000000000 : ℝ)|=(588635517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s0_6 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8302153/16000000 : ℝ)*x 0 + (1177271017/2000000000 : ℝ)*x 1 + (-78144707/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8302153/16000000 : ℝ)^4517 ≤ (21404817939567/50000000000000 : ℝ)^3493 := by
    have hnat : (8302153 : ℕ)^4517*50000000000000^3493 ≤ 21404817939567^3493*16000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8302153 16000000 21404817939567 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1177271017/2000000000 : ℝ)^4517 ≤ (12598393580077/25000000000000 : ℝ)^3493 := by
    have hnat : (1177271017 : ℕ)^4517*25000000000000^3493 ≤ 12598393580077^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177271017 2000000000 12598393580077 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78144707/625000000 : ℝ)^4517 ≤ (6796789786111/100000000000000 : ℝ)^3493 := by
    have hnat : (78144707 : ℕ)^4517*100000000000000^3493 ≤ 6796789786111^3493*625000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78144707 625000000 6796789786111 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8302153/16000000 : ℝ), (1177271017/2000000000 : ℝ), (-78144707/625000000 : ℝ)] ![(21404817939567/50000000000000 : ℝ), (12598393580077/25000000000000 : ℝ), (6796789786111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8302153/16000000 : ℝ)|^4517 ≤ (21404817939567/50000000000000 : ℝ)^3493
        have hw : |(8302153/16000000 : ℝ)|=(8302153/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1177271017/2000000000 : ℝ)|^4517 ≤ (12598393580077/25000000000000 : ℝ)^3493
        have hw : |(1177271017/2000000000 : ℝ)|=(1177271017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78144707/625000000 : ℝ)|^4517 ≤ (6796789786111/100000000000000 : ℝ)^3493
        have hw : |(-78144707/625000000 : ℝ)|=(78144707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s0_7 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (830738683/2000000000 : ℝ)*x 0 + (2715030419/5000000000 : ℝ)*x 1 + (157734581/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (830738683/2000000000 : ℝ)^4517 ≤ (256841693999/800000000000 : ℝ)^3493 := by
    have hnat : (830738683 : ℕ)^4517*800000000000^3493 ≤ 256841693999^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830738683 2000000000 256841693999 800000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715030419/5000000000 : ℝ)^4517 ≤ (22700250124593/50000000000000 : ℝ)^3493 := by
    have hnat : (2715030419 : ℕ)^4517*50000000000000^3493 ≤ 22700250124593^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715030419 5000000000 22700250124593 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157734581/500000000 : ℝ)^4517 ≤ (5623571994963/25000000000000 : ℝ)^3493 := by
    have hnat : (157734581 : ℕ)^4517*25000000000000^3493 ≤ 5623571994963^3493*500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157734581 500000000 5623571994963 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(830738683/2000000000 : ℝ), (2715030419/5000000000 : ℝ), (157734581/500000000 : ℝ)] ![(256841693999/800000000000 : ℝ), (22700250124593/50000000000000 : ℝ), (5623571994963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(830738683/2000000000 : ℝ)|^4517 ≤ (256841693999/800000000000 : ℝ)^3493
        have hw : |(830738683/2000000000 : ℝ)|=(830738683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715030419/5000000000 : ℝ)|^4517 ≤ (22700250124593/50000000000000 : ℝ)^3493
        have hw : |(2715030419/5000000000 : ℝ)|=(2715030419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157734581/500000000 : ℝ)|^4517 ≤ (5623571994963/25000000000000 : ℝ)^3493
        have hw : |(157734581/500000000 : ℝ)|=(157734581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1510_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1401/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2551/10000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4515/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4515 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4515*1^1024 ≤ 0^1024*1^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4515/1024 : ℝ) ≤ (1759588021865770459/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4515 ≤ (1759588021865770459/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4515*100000000000000000000^1024 ≤ 1759588021865770459^1024*5^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1759588021865770459 100000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1759588021865770459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4515 := by
      have hnat : (1 : ℕ)^1024*1^4515 ≤ 1^4515*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101759588021865770459/100000000000000000000 : ℝ) ≤ (1254954836878303/1250000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (101759588021865770459/100000000000000000000 : ℝ)^1024 ≤ (1254954836878303/1250000000000000 : ℝ)^4515 := by
      have hnat : (101759588021865770459 : ℕ)^1024*1250000000000000^4515 ≤ 1254954836878303^4515*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101759588021865770459 100000000000000000000 1254954836878303 1250000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254954836878303/1250000000000000 : ℝ)) (X := (101759588021865770459/100000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51759588021865770459/50000000000000000000 : ℝ) ≤ (629954836878303/625000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (51759588021865770459/50000000000000000000 : ℝ)^1024 ≤ (629954836878303/625000000000000 : ℝ)^4515 := by
      have hnat : (51759588021865770459 : ℕ)^1024*625000000000000^4515 ≤ 629954836878303^4515*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51759588021865770459 50000000000000000000 629954836878303 625000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (629954836878303/625000000000000 : ℝ)) (X := (51759588021865770459/50000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4954836878303/500000000000000 : ℝ)*(0 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4954836878303/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1759588021865770459/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4954836878303/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4515/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4954836878303/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1254954836878303/1250000000000000 : ℝ) by norm_num, show 1+(1759588021865770459/100000000000000000000 : ℝ)+(0 : ℝ)=(101759588021865770459/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1759588021865770459/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4954836878303/500000000000000 : ℝ)*(2/5 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4954836878303/500000000000000 : ℝ)*(2/5 : ℝ)=(629954836878303/625000000000000 : ℝ) by norm_num, show 1+2*(1759588021865770459/100000000000000000000 : ℝ)=(51759588021865770459/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4954836878303/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4954836878303/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4954836878303/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4954836878303/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4954836878303/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4954836878303/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1687957253/10000000000 : ℝ)*X 0 0+(5914369989/10000000000 : ℝ)*X 0 1+(970892157/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2739207737/5000000000 : ℝ)*X 1 0+(-285276217/1250000000 : ℝ)*X 1 1+(4854460719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2739207763/5000000000 : ℝ)*X 2 0+(75850949/156250000 : ℝ)*X 2 1+(-2282209649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2072841723/5000000000 : ℝ)*X 0 0+(386406861/1250000000 : ℝ)*X 0 1+(5491302757/10000000000 : ℝ)*X 0 2+(2072841723/5000000000 : ℝ)*X 1 0+(386406861/1250000000 : ℝ)*X 1 1+(5491302757/10000000000 : ℝ)*X 1 2+(2072841723/5000000000 : ℝ)*X 2 0+(386406861/1250000000 : ℝ)*X 2 1+(5491302757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-845747223/5000000000 : ℝ)*X 0 0+(1220376621/2500000000 : ℝ)*X 0 1+(1471588853/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2594422763/5000000000 : ℝ)*X 1 0+(-1250315329/10000000000 : ℝ)*X 1 1+(588635517/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((8302153/16000000 : ℝ)*X 2 0+(1177271017/2000000000 : ℝ)*X 2 1+(-78144707/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((830738683/2000000000 : ℝ)*X 0 0+(2715030419/5000000000 : ℝ)*X 0 1+(157734581/500000000 : ℝ)*X 0 2+(830738683/2000000000 : ℝ)*X 1 0+(2715030419/5000000000 : ℝ)*X 1 1+(157734581/500000000 : ℝ)*X 1 2+(830738683/2000000000 : ℝ)*X 2 0+(2715030419/5000000000 : ℝ)*X 2 1+(157734581/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (708531810552922516779/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3309771/25000000000000 : ℝ)*(base1) + (27412109/5000000000000 : ℝ)*(base19) + (278598751/50000000000000 : ℝ)*(base23) + (57663351/100000000000000 : ℝ)*(upper3) + (85103323/100000000000000 : ℝ)*(upper5) + (8500881318523/1250000000000 : ℝ)*(major0) + (8500881318523/1250000000000 : ℝ)*(major1) + (8500881318523/1250000000000 : ℝ)*(major2) + (471739393462909/50000000000000 : ℝ)*(sp0) + (943480277814783/100000000000000 : ℝ)*(sp1) + (943480268859461/100000000000000 : ℝ)*(sp2) + (416659239730663/100000000000000 : ℝ)*(sp3) + (205237023/10000000000000 : ℝ)*(sp4) + (171272047/20000000000000 : ℝ)*(sp7) + (208330054664991/50000000000000 : ℝ)*(f.failure) + (943480826056963/100000000000000 : ℝ)*(f.sum) + (309950982313/625000000000000000000000000 : ℝ)*base65 + (3568021333969/625000000000000000000000000 : ℝ)*base67 + (317376773539/156250000000000000000000000 : ℝ)*base70 + (29079682917/19531250000000000000000000 : ℝ)*base71 + (375413896461/78125000000000000000000000 : ℝ)*base73 + (1069382226469/625000000000000000000000000 : ℝ)*base75 + (83110953959/39062500000000000000000000 : ℝ)*base77 + (4777661350219/625000000000000000000000000 : ℝ)*base79 + (49677778957/39062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4812541/500000000000000000000 : ℝ)*base90 + (4812541/500000000000000000000 : ℝ)*base92 + (4812541/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (732747547155339086649/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1143385419/100000000000000 : ℝ)*(base19) + (587367721/50000000000000 : ℝ)*(base23) + (5382631/5000000000000 : ℝ)*(base32) + (82928499/50000000000000 : ℝ)*(upper3) + (3325207/3125000000000 : ℝ)*(upper5) + (1793328988783/250000000000 : ℝ)*(major0) + (1793328988783/250000000000 : ℝ)*(major1) + (1793328988783/250000000000 : ℝ)*(major2) + (1358704573/50000000000000 : ℝ)*(sp1) + (587787841/20000000000000 : ℝ)*(sp2) + (995174062342667/100000000000000 : ℝ)*(sp4) + (497585100774051/50000000000000 : ℝ)*(sp5) + (995169948668021/100000000000000 : ℝ)*(sp6) + (109872206407939/25000000000000 : ℝ)*(sp7) + (54936116660547/12500000000000 : ℝ)*(f.failure) + (995174062342667/100000000000000 : ℝ)*(f.sum) + (1828202703/7812500000000000000000000 : ℝ)*base65 + (1078532530749/125000000000000000000000000 : ℝ)*base67 + (691292009749/125000000000000000000000000 : ℝ)*base69 + (574910125749/125000000000000000000000000 : ℝ)*base71 + (25939042031/15625000000000000000000000 : ℝ)*base73 + (1238072070999/125000000000000000000000000 : ℝ)*base75 + (36621431687/62500000000000000000000000 : ℝ)*base77 + (227025669031/31250000000000000000000000 : ℝ)*base79 + (44486114877/125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1553897/125000000000000000000 : ℝ)*base90 + (1553897/125000000000000000000 : ℝ)*base92 + (1553897/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1510_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1401/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2551/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1510_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1510_s1_0 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-921102861/5000000000 : ℝ)*x 0 + (5571842201/10000000000 : ℝ)*x 1 + (2548929549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (921102861/5000000000 : ℝ)^4517 ≤ (11219314169633/100000000000000 : ℝ)^3493 := by
    have hnat : (921102861 : ℕ)^4517*100000000000000^3493 ≤ 11219314169633^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921102861 5000000000 11219314169633 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5571842201/10000000000 : ℝ)^4517 ≤ (46939276578817/100000000000000 : ℝ)^3493 := by
    have hnat : (5571842201 : ℕ)^4517*100000000000000^3493 ≤ 46939276578817^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5571842201 10000000000 46939276578817 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2548929549/5000000000 : ℝ)^4517 ≤ (41841409234401/100000000000000 : ℝ)^3493 := by
    have hnat : (2548929549 : ℕ)^4517*100000000000000^3493 ≤ 41841409234401^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548929549 5000000000 41841409234401 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-921102861/5000000000 : ℝ), (5571842201/10000000000 : ℝ), (2548929549/5000000000 : ℝ)] ![(11219314169633/100000000000000 : ℝ), (46939276578817/100000000000000 : ℝ), (41841409234401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-921102861/5000000000 : ℝ)|^4517 ≤ (11219314169633/100000000000000 : ℝ)^3493
        have hw : |(-921102861/5000000000 : ℝ)|=(921102861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5571842201/10000000000 : ℝ)|^4517 ≤ (46939276578817/100000000000000 : ℝ)^3493
        have hw : |(5571842201/10000000000 : ℝ)|=(5571842201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2548929549/5000000000 : ℝ)|^4517 ≤ (41841409234401/100000000000000 : ℝ)^3493
        have hw : |(2548929549/5000000000 : ℝ)|=(2548929549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s1_1 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693493469/5000000000 : ℝ)*x 0 + (-2091850619/10000000000 : ℝ)*x 1 + (5097858277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693493469/5000000000 : ℝ)^4517 ≤ (44935326250229/100000000000000 : ℝ)^3493 := by
    have hnat : (2693493469 : ℕ)^4517*100000000000000^3493 ≤ 44935326250229^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693493469 5000000000 44935326250229 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091850619/10000000000 : ℝ)^4517 ≤ (13223273218067/100000000000000 : ℝ)^3493 := by
    have hnat : (2091850619 : ℕ)^4517*100000000000000^3493 ≤ 13223273218067^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091850619 10000000000 13223273218067 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5097858277/10000000000 : ℝ)^4517 ≤ (4184140052049/10000000000000 : ℝ)^3493 := by
    have hnat : (5097858277 : ℕ)^4517*10000000000000^3493 ≤ 4184140052049^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097858277 10000000000 4184140052049 10000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693493469/5000000000 : ℝ), (-2091850619/10000000000 : ℝ), (5097858277/10000000000 : ℝ)] ![(44935326250229/100000000000000 : ℝ), (13223273218067/100000000000000 : ℝ), (4184140052049/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693493469/5000000000 : ℝ)|^4517 ≤ (44935326250229/100000000000000 : ℝ)^3493
        have hw : |(2693493469/5000000000 : ℝ)|=(2693493469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091850619/10000000000 : ℝ)|^4517 ≤ (13223273218067/100000000000000 : ℝ)^3493
        have hw : |(-2091850619/10000000000 : ℝ)|=(2091850619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5097858277/10000000000 : ℝ)|^4517 ≤ (4184140052049/10000000000000 : ℝ)^3493
        have hw : |(5097858277/10000000000 : ℝ)|=(5097858277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s1_2 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673373289/1250000000 : ℝ)*x 0 + (1274464737/2500000000 : ℝ)*x 1 + (-1045925287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673373289/1250000000 : ℝ)^4517 ≤ (44935319497679/100000000000000 : ℝ)^3493 := by
    have hnat : (673373289 : ℕ)^4517*100000000000000^3493 ≤ 44935319497679^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673373289 1250000000 44935319497679 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1274464737/2500000000 : ℝ)^4517 ≤ (20920703821167/50000000000000 : ℝ)^3493 := by
    have hnat : (1274464737 : ℕ)^4517*50000000000000^3493 ≤ 20920703821167^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274464737 2500000000 20920703821167 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045925287/5000000000 : ℝ)^4517 ≤ (2644654570043/20000000000000 : ℝ)^3493 := by
    have hnat : (1045925287 : ℕ)^4517*20000000000000^3493 ≤ 2644654570043^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045925287 5000000000 2644654570043 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673373289/1250000000 : ℝ), (1274464737/2500000000 : ℝ), (-1045925287/5000000000 : ℝ)] ![(44935319497679/100000000000000 : ℝ), (20920703821167/50000000000000 : ℝ), (2644654570043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673373289/1250000000 : ℝ)|^4517 ≤ (44935319497679/100000000000000 : ℝ)^3493
        have hw : |(673373289/1250000000 : ℝ)|=(673373289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1274464737/2500000000 : ℝ)|^4517 ≤ (20920703821167/50000000000000 : ℝ)^3493
        have hw : |(1274464737/2500000000 : ℝ)|=(1274464737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1045925287/5000000000 : ℝ)|^4517 ≤ (2644654570043/20000000000000 : ℝ)^3493
        have hw : |(-1045925287/5000000000 : ℝ)|=(1045925287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s1_3 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062585461/2500000000 : ℝ)*x 0 + (3742352439/10000000000 : ℝ)*x 1 + (481563591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062585461/2500000000 : ℝ)^4517 ≤ (16537255725591/50000000000000 : ℝ)^3493 := by
    have hnat : (1062585461 : ℕ)^4517*50000000000000^3493 ≤ 16537255725591^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062585461 2500000000 16537255725591 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3742352439/10000000000 : ℝ)^4517 ≤ (1402745061173/5000000000000 : ℝ)^3493 := by
    have hnat : (3742352439 : ℕ)^4517*5000000000000^3493 ≤ 1402745061173^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3742352439 10000000000 1402745061173 5000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481563591/1000000000 : ℝ)^4517 ≤ (38870587309477/100000000000000 : ℝ)^3493 := by
    have hnat : (481563591 : ℕ)^4517*100000000000000^3493 ≤ 38870587309477^3493*1000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481563591 1000000000 38870587309477 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062585461/2500000000 : ℝ), (3742352439/10000000000 : ℝ), (481563591/1000000000 : ℝ)] ![(16537255725591/50000000000000 : ℝ), (1402745061173/5000000000000 : ℝ), (38870587309477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062585461/2500000000 : ℝ)|^4517 ≤ (16537255725591/50000000000000 : ℝ)^3493
        have hw : |(1062585461/2500000000 : ℝ)|=(1062585461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3742352439/10000000000 : ℝ)|^4517 ≤ (1402745061173/5000000000000 : ℝ)^3493
        have hw : |(3742352439/10000000000 : ℝ)|=(3742352439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(481563591/1000000000 : ℝ)|^4517 ≤ (38870587309477/100000000000000 : ℝ)^3493
        have hw : |(481563591/1000000000 : ℝ)|=(481563591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s1_4 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1842511411/10000000000 : ℝ)*x 0 + (5103174609/10000000000 : ℝ)*x 1 + (2783220443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1842511411/10000000000 : ℝ)^4517 ≤ (2805430422627/25000000000000 : ℝ)^3493 := by
    have hnat : (1842511411 : ℕ)^4517*25000000000000^3493 ≤ 2805430422627^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842511411 10000000000 2805430422627 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5103174609/10000000000 : ℝ)^4517 ≤ (41897835506231/100000000000000 : ℝ)^3493 := by
    have hnat : (5103174609 : ℕ)^4517*100000000000000^3493 ≤ 41897835506231^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5103174609 10000000000 41897835506231 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2783220443/5000000000 : ℝ)^4517 ≤ (46880442783441/100000000000000 : ℝ)^3493 := by
    have hnat : (2783220443 : ℕ)^4517*100000000000000^3493 ≤ 46880442783441^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783220443 5000000000 46880442783441 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1842511411/10000000000 : ℝ), (5103174609/10000000000 : ℝ), (2783220443/5000000000 : ℝ)] ![(2805430422627/25000000000000 : ℝ), (41897835506231/100000000000000 : ℝ), (46880442783441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1842511411/10000000000 : ℝ)|^4517 ≤ (2805430422627/25000000000000 : ℝ)^3493
        have hw : |(-1842511411/10000000000 : ℝ)|=(1842511411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5103174609/10000000000 : ℝ)|^4517 ≤ (41897835506231/100000000000000 : ℝ)^3493
        have hw : |(5103174609/10000000000 : ℝ)|=(5103174609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2783220443/5000000000 : ℝ)|^4517 ≤ (46880442783441/100000000000000 : ℝ)^3493
        have hw : |(2783220443/5000000000 : ℝ)|=(2783220443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s1_5 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631085937/5000000000 : ℝ)*x 0 + (-1623268217/10000000000 : ℝ)*x 1 + (2783220529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631085937/5000000000 : ℝ)^4517 ≤ (4359356617037/10000000000000 : ℝ)^3493 := by
    have hnat : (2631085937 : ℕ)^4517*10000000000000^3493 ≤ 4359356617037^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631085937 5000000000 4359356617037 10000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1623268217/10000000000 : ℝ)^4517 ≤ (4762994577977/50000000000000 : ℝ)^3493 := by
    have hnat : (1623268217 : ℕ)^4517*50000000000000^3493 ≤ 4762994577977^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623268217 10000000000 4762994577977 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2783220529/5000000000 : ℝ)^4517 ≤ (11720111164171/25000000000000 : ℝ)^3493 := by
    have hnat : (2783220529 : ℕ)^4517*25000000000000^3493 ≤ 11720111164171^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783220529 5000000000 11720111164171 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631085937/5000000000 : ℝ), (-1623268217/10000000000 : ℝ), (2783220529/5000000000 : ℝ)] ![(4359356617037/10000000000000 : ℝ), (4762994577977/50000000000000 : ℝ), (11720111164171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631085937/5000000000 : ℝ)|^4517 ≤ (4359356617037/10000000000000 : ℝ)^3493
        have hw : |(2631085937/5000000000 : ℝ)|=(2631085937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1623268217/10000000000 : ℝ)|^4517 ≤ (4762994577977/50000000000000 : ℝ)^3493
        have hw : |(-1623268217/10000000000 : ℝ)|=(1623268217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2783220529/5000000000 : ℝ)|^4517 ≤ (11720111164171/25000000000000 : ℝ)^3493
        have hw : |(2783220529/5000000000 : ℝ)|=(2783220529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s1_6 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526217167/1000000000 : ℝ)*x 0 + (278322057/500000000 : ℝ)*x 1 + (-405817097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526217167/1000000000 : ℝ)^4517 ≤ (43593563984929/100000000000000 : ℝ)^3493 := by
    have hnat : (526217167 : ℕ)^4517*100000000000000^3493 ≤ 43593563984929^3493*1000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526217167 1000000000 43593563984929 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278322057/500000000 : ℝ)^4517 ≤ (23440222774871/50000000000000 : ℝ)^3493 := by
    have hnat : (278322057 : ℕ)^4517*50000000000000^3493 ≤ 23440222774871^3493*500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278322057 500000000 23440222774871 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405817097/2500000000 : ℝ)^4517 ≤ (9525990453633/100000000000000 : ℝ)^3493 := by
    have hnat : (405817097 : ℕ)^4517*100000000000000^3493 ≤ 9525990453633^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405817097 2500000000 9525990453633 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526217167/1000000000 : ℝ), (278322057/500000000 : ℝ), (-405817097/2500000000 : ℝ)] ![(43593563984929/100000000000000 : ℝ), (23440222774871/50000000000000 : ℝ), (9525990453633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526217167/1000000000 : ℝ)|^4517 ≤ (43593563984929/100000000000000 : ℝ)^3493
        have hw : |(526217167/1000000000 : ℝ)|=(526217167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278322057/500000000 : ℝ)|^4517 ≤ (23440222774871/50000000000000 : ℝ)^3493
        have hw : |(278322057/500000000 : ℝ)|=(278322057/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-405817097/2500000000 : ℝ)|^4517 ≤ (9525990453633/100000000000000 : ℝ)^3493
        have hw : |(-405817097/2500000000 : ℝ)|=(405817097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s1_7 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4251034369/10000000000 : ℝ)*x 0 + (2401799771/5000000000 : ℝ)*x 1 + (1877291389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251034369/10000000000 : ℝ)^4517 ≤ (33081480394139/100000000000000 : ℝ)^3493 := by
    have hnat : (4251034369 : ℕ)^4517*100000000000000^3493 ≤ 33081480394139^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251034369 10000000000 33081480394139 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2401799771/5000000000 : ℝ)^4517 ≤ (302695291193/781250000000 : ℝ)^3493 := by
    have hnat : (2401799771 : ℕ)^4517*781250000000^3493 ≤ 302695291193^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401799771 5000000000 302695291193 781250000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877291389/5000000000 : ℝ)^4517 ≤ (7043380576991/25000000000000 : ℝ)^3493 := by
    have hnat : (1877291389 : ℕ)^4517*25000000000000^3493 ≤ 7043380576991^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877291389 5000000000 7043380576991 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251034369/10000000000 : ℝ), (2401799771/5000000000 : ℝ), (1877291389/5000000000 : ℝ)] ![(33081480394139/100000000000000 : ℝ), (302695291193/781250000000 : ℝ), (7043380576991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251034369/10000000000 : ℝ)|^4517 ≤ (33081480394139/100000000000000 : ℝ)^3493
        have hw : |(4251034369/10000000000 : ℝ)|=(4251034369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2401799771/5000000000 : ℝ)|^4517 ≤ (302695291193/781250000000 : ℝ)^3493
        have hw : |(2401799771/5000000000 : ℝ)|=(2401799771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1877291389/5000000000 : ℝ)|^4517 ≤ (7043380576991/25000000000000 : ℝ)^3493
        have hw : |(1877291389/5000000000 : ℝ)|=(1877291389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1510_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2551/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1401/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8329/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9177/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2551/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1401/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2551/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1401/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2551/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1401/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2551/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1401/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2551/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1401/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2551/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1401/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1401/50000 : ℝ) ^ (4515/1024 : ℝ) ≤ (1427604863389/10000000000000000000 : ℝ) := by
    have hpowers : (1401/50000 : ℝ)^4515 ≤ (1427604863389/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1401 : ℕ)^4515*10000000000000000000^1024 ≤ 1427604863389^1024*50000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 50000 1427604863389 10000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/50000 : ℝ)) (X := (1427604863389/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2551/10000 : ℝ) ^ (4515/1024 : ℝ) ≤ (121073698612221671/50000000000000000000 : ℝ) := by
    have hpowers : (2551/10000 : ℝ)^4515 ≤ (121073698612221671/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2551 : ℕ)^4515*50000000000000000000^1024 ≤ 121073698612221671^1024*10000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2551 10000 121073698612221671 50000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2551/10000 : ℝ)) (X := (121073698612221671/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000001427604863389/5000000000000000000 : ℝ) ≤ (1000000064756023/1000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (5000001427604863389/5000000000000000000 : ℝ)^1024 ≤ (1000000064756023/1000000000000000 : ℝ)^4515 := by
      have hnat : (5000001427604863389 : ℕ)^1024*1000000000000000^4515 ≤ 1000000064756023^4515*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000001427604863389 5000000000000000000 1000000064756023 1000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000064756023/1000000000000000 : ℝ)) (X := (5000001427604863389/5000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6265135104579567327/6250000000000000000 : ℝ) ≤ (10005487081570897/10000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (6265135104579567327/6250000000000000000 : ℝ)^1024 ≤ (10005487081570897/10000000000000000 : ℝ)^4515 := by
      have hnat : (6265135104579567327 : ℕ)^1024*10000000000000000^4515 ≤ 10005487081570897^4515*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6265135104579567327 6250000000000000000 10005487081570897 10000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005487081570897/10000000000000000 : ℝ)) (X := (6265135104579567327/6250000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25121073698612221671/25000000000000000000 : ℝ) ≤ (2502743378895391/2500000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (25121073698612221671/25000000000000000000 : ℝ)^1024 ≤ (2502743378895391/2500000000000000 : ℝ)^4515 := by
      have hnat : (25121073698612221671 : ℕ)^1024*2500000000000000^4515 ≤ 2502743378895391^4515*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25121073698612221671 25000000000000000000 2502743378895391 2500000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502743378895391/2500000000000000 : ℝ)) (X := (25121073698612221671/25000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1427604863389/10000000000000000000 : ℝ) ≤ ((56762317182150481243/56770000000000000000 : ℝ)+2*(5486434010667/2270800000000000 : ℝ)*(1401/50000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (56762317182150481243/56770000000000000000 : ℝ)+2*(5486434010667/2270800000000000 : ℝ)*(1401/50000 : ℝ)=(1000000064756023/1000000000000000 : ℝ) by norm_num, show 1+2*(1427604863389/10000000000000000000 : ℝ)=(5000001427604863389/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(121073698612221671/50000000000000000000 : ℝ)+(1427604863389/10000000000000000000 : ℝ) ≤ ((56762317182150481243/56770000000000000000 : ℝ)+(5486434010667/2270800000000000 : ℝ)*((2551/10000 : ℝ)+(1401/50000 : ℝ)))^(4515/1024 : ℝ) := by
    rw [show (56762317182150481243/56770000000000000000 : ℝ)+(5486434010667/2270800000000000 : ℝ)*((2551/10000 : ℝ)+(1401/50000 : ℝ))=(10005487081570897/10000000000000000 : ℝ) by norm_num, show 1+(121073698612221671/50000000000000000000 : ℝ)+(1427604863389/10000000000000000000 : ℝ)=(6265135104579567327/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(121073698612221671/50000000000000000000 : ℝ) ≤ ((56762317182150481243/56770000000000000000 : ℝ)+2*(5486434010667/2270800000000000 : ℝ)*(2551/10000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (56762317182150481243/56770000000000000000 : ℝ)+2*(5486434010667/2270800000000000 : ℝ)*(2551/10000 : ℝ)=(2502743378895391/2500000000000000 : ℝ) by norm_num, show 1+2*(121073698612221671/50000000000000000000 : ℝ)=(25121073698612221671/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56762317182150481243/56770000000000000000 : ℝ)*(X 1 0+X 2 0)+(5486434010667/2270800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (1401/50000 : ℝ)) (hi := (2551/10000 : ℝ)) (c := (56762317182150481243/56770000000000000000 : ℝ)) (alpha := (5486434010667/2270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56762317182150481243/56770000000000000000 : ℝ)*(X 0 1+X 2 1)+(5486434010667/2270800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (1401/50000 : ℝ)) (hi := (2551/10000 : ℝ)) (c := (56762317182150481243/56770000000000000000 : ℝ)) (alpha := (5486434010667/2270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56762317182150481243/56770000000000000000 : ℝ)*(X 0 2+X 1 2)+(5486434010667/2270800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (1401/50000 : ℝ)) (hi := (2551/10000 : ℝ)) (c := (56762317182150481243/56770000000000000000 : ℝ)) (alpha := (5486434010667/2270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-921102861/5000000000 : ℝ)*X 0 0+(5571842201/10000000000 : ℝ)*X 0 1+(2548929549/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2693493469/5000000000 : ℝ)*X 1 0+(-2091850619/10000000000 : ℝ)*X 1 1+(5097858277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((673373289/1250000000 : ℝ)*X 2 0+(1274464737/2500000000 : ℝ)*X 2 1+(-1045925287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1062585461/2500000000 : ℝ)*X 0 0+(3742352439/10000000000 : ℝ)*X 0 1+(481563591/1000000000 : ℝ)*X 0 2+(1062585461/2500000000 : ℝ)*X 1 0+(3742352439/10000000000 : ℝ)*X 1 1+(481563591/1000000000 : ℝ)*X 1 2+(1062585461/2500000000 : ℝ)*X 2 0+(3742352439/10000000000 : ℝ)*X 2 1+(481563591/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1842511411/10000000000 : ℝ)*X 0 0+(5103174609/10000000000 : ℝ)*X 0 1+(2783220443/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2631085937/5000000000 : ℝ)*X 1 0+(-1623268217/10000000000 : ℝ)*X 1 1+(2783220529/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((526217167/1000000000 : ℝ)*X 2 0+(278322057/500000000 : ℝ)*X 2 1+(-405817097/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4251034369/10000000000 : ℝ)*X 0 0+(2401799771/5000000000 : ℝ)*X 0 1+(1877291389/5000000000 : ℝ)*X 0 2+(4251034369/10000000000 : ℝ)*X 1 0+(2401799771/5000000000 : ℝ)*X 1 1+(1877291389/5000000000 : ℝ)*X 1 2+(4251034369/10000000000 : ℝ)*X 2 0+(2401799771/5000000000 : ℝ)*X 2 1+(1877291389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (682191794353174911588829293/81100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44331919/100000000000000 : ℝ)*(base1) + (446505571/25000000000000 : ℝ)*(base19) + (38521271/2500000000000 : ℝ)*(base23) + (33481691/20000000000000 : ℝ)*(upper3) + (28001499/20000000000000 : ℝ)*(upper5) + (304153398270181/20000000000000 : ℝ)*(major0) + (304153398270181/20000000000000 : ℝ)*(major1) + (304153398270181/20000000000000 : ℝ)*(major2) + (421958313062209/20000000000000 : ℝ)*(sp0) + (1054900334084523/50000000000000 : ℝ)*(sp1) + (210980091334049/10000000000000 : ℝ)*(sp2) + (116465719812861/12500000000000 : ℝ)*(sp3) + (2733303051/25000000000000 : ℝ)*(sp4) + (2722642231/50000000000000 : ℝ)*(sp7) + (232932812029817/25000000000000 : ℝ)*(f.failure) + (210980245419133/10000000000000 : ℝ)*(f.sum) + (26998127247401/22708000000000000000000000000 : ℝ)*base66 + (1811275587203089983/1135400000000000000000000000000000 : ℝ)*base67 + (7383437897513110017/1135400000000000000000000000000000 : ℝ)*base70 + (3167955919264310017/1135400000000000000000000000000000 : ℝ)*base72 + (52087291442769/22708000000000000000000000000 : ℝ)*base74 + (1729982376671689983/1135400000000000000000000000000000 : ℝ)*base75 + (2909327384222889983/1135400000000000000000000000000000 : ℝ)*base77 + (5179932179442489983/1135400000000000000000000000000000 : ℝ)*base79 + (193268411288521/22708000000000000000000000000 : ℝ)*base82 + (2946667/250000000000000000000 : ℝ)*base90 + (2946667/250000000000000000000 : ℝ)*base92 + (2946667/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132711233609612664935888037/40550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (659737867/100000000000000 : ℝ)*(base19) + (159098859/25000000000000 : ℝ)*(base23) + (54415723/50000000000000 : ℝ)*(upper3) + (5182799/20000000000000 : ℝ)*(lower4) + (4239689/100000000000000 : ℝ)*(upper5) + (311185796281071/20000000000000 : ℝ)*(major0) + (311185796281071/20000000000000 : ℝ)*(major1) + (311185796281071/20000000000000 : ℝ)*(major2) + (2355985717/50000000000000 : ℝ)*(sp1) + (103594281/2000000000000 : ℝ)*(sp2) + (2158583841279109/100000000000000 : ℝ)*(sp4) + (134911154348113/6250000000000 : ℝ)*(sp5) + (2158578025169623/100000000000000 : ℝ)*(sp6) + (59579625777433/6250000000000 : ℝ)*(sp7) + (59579625777433/6250000000000 : ℝ)*(f.failure) + (2158583841279109/100000000000000 : ℝ)*(f.sum) + (26281893113807/22708000000000000000000000000 : ℝ)*base66 + (4602298433987423747/1135400000000000000000000000000000 : ℝ)*base68 + (788446560597176253/1135400000000000000000000000000000 : ℝ)*base69 + (3395494670996023747/1135400000000000000000000000000000 : ℝ)*base72 + (3704320253479/4541600000000000000000000000 : ℝ)*base74 + (1229824025186023747/1135400000000000000000000000000000 : ℝ)*base76 + (2027286266896423747/1135400000000000000000000000000000 : ℝ)*base78 + (1977669461748023747/1135400000000000000000000000000000 : ℝ)*base80 + (74306918655877/22708000000000000000000000000 : ℝ)*base81 + (98083/62500000000000000000 : ℝ)*base90 + (98083/62500000000000000000 : ℝ)*base92 + (98083/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1510_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2551/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1401/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8329/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9177/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1510_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1510_s2_0 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-466739013/2500000000 : ℝ)*x 0 + (5458560387/10000000000 : ℝ)*x 1 + (5195112249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466739013/2500000000 : ℝ)^4517 ≤ (11414618743619/100000000000000 : ℝ)^3493 := by
    have hnat : (466739013 : ℕ)^4517*100000000000000^3493 ≤ 11414618743619^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466739013 2500000000 11414618743619 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458560387/10000000000 : ℝ)^4517 ≤ (11427218784227/25000000000000 : ℝ)^3493 := by
    have hnat : (5458560387 : ℕ)^4517*25000000000000^3493 ≤ 11427218784227^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458560387 10000000000 11427218784227 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195112249/10000000000 : ℝ)^4517 ≤ (1071912652581/2500000000000 : ℝ)^3493 := by
    have hnat : (5195112249 : ℕ)^4517*2500000000000^3493 ≤ 1071912652581^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195112249 10000000000 1071912652581 2500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-466739013/2500000000 : ℝ), (5458560387/10000000000 : ℝ), (5195112249/10000000000 : ℝ)] ![(11414618743619/100000000000000 : ℝ), (11427218784227/25000000000000 : ℝ), (1071912652581/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-466739013/2500000000 : ℝ)|^4517 ≤ (11414618743619/100000000000000 : ℝ)^3493
        have hw : |(-466739013/2500000000 : ℝ)|=(466739013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458560387/10000000000 : ℝ)|^4517 ≤ (11427218784227/25000000000000 : ℝ)^3493
        have hw : |(5458560387/10000000000 : ℝ)|=(5458560387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195112249/10000000000 : ℝ)|^4517 ≤ (1071912652581/2500000000000 : ℝ)^3493
        have hw : |(5195112249/10000000000 : ℝ)|=(5195112249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s2_1 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358220029/10000000000 : ℝ)*x 0 + (-2002590343/10000000000 : ℝ)*x 1 + (5195112257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358220029/10000000000 : ℝ)^4517 ≤ (5578158242389/12500000000000 : ℝ)^3493 := by
    have hnat : (5358220029 : ℕ)^4517*12500000000000^3493 ≤ 5578158242389^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358220029 10000000000 5578158242389 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002590343/10000000000 : ℝ)^4517 ≤ (12498227863221/100000000000000 : ℝ)^3493 := by
    have hnat : (2002590343 : ℕ)^4517*100000000000000^3493 ≤ 12498227863221^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002590343 10000000000 12498227863221 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195112257/10000000000 : ℝ)^4517 ≤ (21438253094311/50000000000000 : ℝ)^3493 := by
    have hnat : (5195112257 : ℕ)^4517*50000000000000^3493 ≤ 21438253094311^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195112257 10000000000 21438253094311 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358220029/10000000000 : ℝ), (-2002590343/10000000000 : ℝ), (5195112257/10000000000 : ℝ)] ![(5578158242389/12500000000000 : ℝ), (12498227863221/100000000000000 : ℝ), (21438253094311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358220029/10000000000 : ℝ)|^4517 ≤ (5578158242389/12500000000000 : ℝ)^3493
        have hw : |(5358220029/10000000000 : ℝ)|=(5358220029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2002590343/10000000000 : ℝ)|^4517 ≤ (12498227863221/100000000000000 : ℝ)^3493
        have hw : |(-2002590343/10000000000 : ℝ)|=(2002590343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195112257/10000000000 : ℝ)|^4517 ≤ (21438253094311/50000000000000 : ℝ)^3493
        have hw : |(5195112257/10000000000 : ℝ)|=(5195112257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s2_2 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679109961/5000000000 : ℝ)*x 0 + (5195112313/10000000000 : ℝ)*x 1 + (-2002590411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679109961/5000000000 : ℝ)^4517 ≤ (11156316196683/25000000000000 : ℝ)^3493 := by
    have hnat : (2679109961 : ℕ)^4517*25000000000000^3493 ≤ 11156316196683^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679109961 5000000000 11156316196683 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195112313/10000000000 : ℝ)^4517 ≤ (5359563348287/12500000000000 : ℝ)^3493 := by
    have hnat : (5195112313 : ℕ)^4517*12500000000000^3493 ≤ 5359563348287^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195112313 10000000000 5359563348287 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2002590411/10000000000 : ℝ)^4517 ≤ (499929136481/4000000000000 : ℝ)^3493 := by
    have hnat : (2002590411 : ℕ)^4517*4000000000000^3493 ≤ 499929136481^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002590411 10000000000 499929136481 4000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679109961/5000000000 : ℝ), (5195112313/10000000000 : ℝ), (-2002590411/10000000000 : ℝ)] ![(11156316196683/25000000000000 : ℝ), (5359563348287/12500000000000 : ℝ), (499929136481/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679109961/5000000000 : ℝ)|^4517 ≤ (11156316196683/25000000000000 : ℝ)^3493
        have hw : |(2679109961/5000000000 : ℝ)|=(2679109961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195112313/10000000000 : ℝ)|^4517 ≤ (5359563348287/12500000000000 : ℝ)^3493
        have hw : |(5195112313/10000000000 : ℝ)|=(5195112313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2002590411/10000000000 : ℝ)|^4517 ≤ (499929136481/4000000000000 : ℝ)^3493
        have hw : |(-2002590411/10000000000 : ℝ)|=(2002590411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s2_3 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268102017/10000000000 : ℝ)*x 0 + (397868231/1000000000 : ℝ)*x 1 + (4575230829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268102017/10000000000 : ℝ)^4517 ≤ (16626669398299/50000000000000 : ℝ)^3493 := by
    have hnat : (4268102017 : ℕ)^4517*50000000000000^3493 ≤ 16626669398299^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268102017 10000000000 16626669398299 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397868231/1000000000 : ℝ)^4517 ≤ (1214673955363/4000000000000 : ℝ)^3493 := by
    have hnat : (397868231 : ℕ)^4517*4000000000000^3493 ≤ 1214673955363^3493*1000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397868231 1000000000 1214673955363 4000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4575230829/10000000000 : ℝ)^4517 ≤ (4547476537467/12500000000000 : ℝ)^3493 := by
    have hnat : (4575230829 : ℕ)^4517*12500000000000^3493 ≤ 4547476537467^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575230829 10000000000 4547476537467 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268102017/10000000000 : ℝ), (397868231/1000000000 : ℝ), (4575230829/10000000000 : ℝ)] ![(16626669398299/50000000000000 : ℝ), (1214673955363/4000000000000 : ℝ), (4547476537467/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268102017/10000000000 : ℝ)|^4517 ≤ (16626669398299/50000000000000 : ℝ)^3493
        have hw : |(4268102017/10000000000 : ℝ)|=(4268102017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(397868231/1000000000 : ℝ)|^4517 ≤ (1214673955363/4000000000000 : ℝ)^3493
        have hw : |(397868231/1000000000 : ℝ)|=(397868231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4575230829/10000000000 : ℝ)|^4517 ≤ (4547476537467/12500000000000 : ℝ)^3493
        have hw : |(4575230829/10000000000 : ℝ)|=(4575230829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s2_4 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1867007947/10000000000 : ℝ)*x 0 + (2598382137/5000000000 : ℝ)*x 1 + (1091378821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1867007947/10000000000 : ℝ)^4517 ≤ (2283005809591/20000000000000 : ℝ)^3493 := by
    have hnat : (1867007947 : ℕ)^4517*20000000000000^3493 ≤ 2283005809591^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867007947 10000000000 2283005809591 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598382137/5000000000 : ℝ)^4517 ≤ (42894138559459/100000000000000 : ℝ)^3493 := by
    have hnat : (2598382137 : ℕ)^4517*100000000000000^3493 ≤ 42894138559459^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598382137 5000000000 42894138559459 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091378821/2000000000 : ℝ)^4517 ≤ (45690832376249/100000000000000 : ℝ)^3493 := by
    have hnat : (1091378821 : ℕ)^4517*100000000000000^3493 ≤ 45690832376249^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091378821 2000000000 45690832376249 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1867007947/10000000000 : ℝ), (2598382137/5000000000 : ℝ), (1091378821/2000000000 : ℝ)] ![(2283005809591/20000000000000 : ℝ), (42894138559459/100000000000000 : ℝ), (45690832376249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1867007947/10000000000 : ℝ)|^4517 ≤ (2283005809591/20000000000000 : ℝ)^3493
        have hw : |(-1867007947/10000000000 : ℝ)|=(1867007947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2598382137/5000000000 : ℝ)|^4517 ≤ (42894138559459/100000000000000 : ℝ)^3493
        have hw : |(2598382137/5000000000 : ℝ)|=(2598382137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091378821/2000000000 : ℝ)|^4517 ≤ (45690832376249/100000000000000 : ℝ)^3493
        have hw : |(1091378821/2000000000 : ℝ)|=(1091378821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s2_5 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057812703/2000000000 : ℝ)*x 0 + (-1740808453/10000000000 : ℝ)*x 1 + (5456895201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057812703/2000000000 : ℝ)^4517 ≤ (43881870380357/100000000000000 : ℝ)^3493 := by
    have hnat : (1057812703 : ℕ)^4517*100000000000000^3493 ≤ 43881870380357^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057812703 2000000000 43881870380357 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1740808453/10000000000 : ℝ)^4517 ≤ (208545707249/2000000000000 : ℝ)^3493 := by
    have hnat : (1740808453 : ℕ)^4517*2000000000000^3493 ≤ 208545707249^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740808453 10000000000 208545707249 2000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456895201/10000000000 : ℝ)^4517 ≤ (45690844243377/100000000000000 : ℝ)^3493 := by
    have hnat : (5456895201 : ℕ)^4517*100000000000000^3493 ≤ 45690844243377^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456895201 10000000000 45690844243377 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057812703/2000000000 : ℝ), (-1740808453/10000000000 : ℝ), (5456895201/10000000000 : ℝ)] ![(43881870380357/100000000000000 : ℝ), (208545707249/2000000000000 : ℝ), (45690844243377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057812703/2000000000 : ℝ)|^4517 ≤ (43881870380357/100000000000000 : ℝ)^3493
        have hw : |(1057812703/2000000000 : ℝ)|=(1057812703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1740808453/10000000000 : ℝ)|^4517 ≤ (208545707249/2000000000000 : ℝ)^3493
        have hw : |(-1740808453/10000000000 : ℝ)|=(1740808453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456895201/10000000000 : ℝ)|^4517 ≤ (45690844243377/100000000000000 : ℝ)^3493
        have hw : |(5456895201/10000000000 : ℝ)|=(5456895201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s2_6 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322266023/2500000000 : ℝ)*x 0 + (5456894439/10000000000 : ℝ)*x 1 + (-1740808719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322266023/2500000000 : ℝ)^4517 ≤ (4388187657097/10000000000000 : ℝ)^3493 := by
    have hnat : (1322266023 : ℕ)^4517*10000000000000^3493 ≤ 4388187657097^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322266023 2500000000 4388187657097 10000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456894439/10000000000 : ℝ)^4517 ≤ (45690835992691/100000000000000 : ℝ)^3493 := by
    have hnat : (5456894439 : ℕ)^4517*100000000000000^3493 ≤ 45690835992691^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456894439 10000000000 45690835992691 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1740808719/10000000000 : ℝ)^4517 ≤ (10427287422859/100000000000000 : ℝ)^3493 := by
    have hnat : (1740808719 : ℕ)^4517*100000000000000^3493 ≤ 10427287422859^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740808719 10000000000 10427287422859 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322266023/2500000000 : ℝ), (5456894439/10000000000 : ℝ), (-1740808719/10000000000 : ℝ)] ![(4388187657097/10000000000000 : ℝ), (45690835992691/100000000000000 : ℝ), (10427287422859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322266023/2500000000 : ℝ)|^4517 ≤ (4388187657097/10000000000000 : ℝ)^3493
        have hw : |(1322266023/2500000000 : ℝ)|=(1322266023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456894439/10000000000 : ℝ)|^4517 ≤ (45690835992691/100000000000000 : ℝ)^3493
        have hw : |(5456894439/10000000000 : ℝ)|=(5456894439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1740808719/10000000000 : ℝ)|^4517 ≤ (10427287422859/100000000000000 : ℝ)^3493
        have hw : |(-1740808719/10000000000 : ℝ)|=(1740808719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s2_7 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268221871/10000000000 : ℝ)*x 0 + (4571492963/10000000000 : ℝ)*x 1 + (796490621/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268221871/10000000000 : ℝ)^4517 ≤ (33254546349847/100000000000000 : ℝ)^3493 := by
    have hnat : (4268221871 : ℕ)^4517*100000000000000^3493 ≤ 33254546349847^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268221871 10000000000 33254546349847 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4571492963/10000000000 : ℝ)^4517 ≤ (18170691137833/50000000000000 : ℝ)^3493 := by
    have hnat : (4571492963 : ℕ)^4517*50000000000000^3493 ≤ 18170691137833^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4571492963 10000000000 18170691137833 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796490621/2000000000 : ℝ)^4517 ≤ (7601017838921/25000000000000 : ℝ)^3493 := by
    have hnat : (796490621 : ℕ)^4517*25000000000000^3493 ≤ 7601017838921^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796490621 2000000000 7601017838921 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268221871/10000000000 : ℝ), (4571492963/10000000000 : ℝ), (796490621/2000000000 : ℝ)] ![(33254546349847/100000000000000 : ℝ), (18170691137833/50000000000000 : ℝ), (7601017838921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268221871/10000000000 : ℝ)|^4517 ≤ (33254546349847/100000000000000 : ℝ)^3493
        have hw : |(4268221871/10000000000 : ℝ)|=(4268221871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4571492963/10000000000 : ℝ)|^4517 ≤ (18170691137833/50000000000000 : ℝ)^3493
        have hw : |(4571492963/10000000000 : ℝ)|=(4571492963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796490621/2000000000 : ℝ)|^4517 ≤ (7601017838921/25000000000000 : ℝ)^3493
        have hw : |(796490621/2000000000 : ℝ)|=(796490621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1510_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9177/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8329/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2607/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4001/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9177/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8329/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9177/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8329/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9177/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8329/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9177/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8329/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9177/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8329/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9177/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8329/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8329/100000 : ℝ) ^ (4515/1024 : ℝ) ≤ (1740603982937199/100000000000000000000 : ℝ) := by
    have hpowers : (8329/100000 : ℝ)^4515 ≤ (1740603982937199/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8329 : ℕ)^4515*100000000000000000000^1024 ≤ 1740603982937199^1024*100000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8329 100000 1740603982937199 100000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8329/100000 : ℝ)) (X := (1740603982937199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9177/50000 : ℝ) ^ (4515/1024 : ℝ) ≤ (28354793116703871/50000000000000000000 : ℝ) := by
    have hpowers : (9177/50000 : ℝ)^4515 ≤ (28354793116703871/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9177 : ℕ)^4515*50000000000000000000^1024 ≤ 28354793116703871^1024*50000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9177 50000 28354793116703871 50000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9177/50000 : ℝ)) (X := (28354793116703871/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001740603982937199/50000000000000000000 : ℝ) ≤ (1250009869072487/1250000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (50001740603982937199/50000000000000000000 : ℝ)^1024 ≤ (1250009869072487/1250000000000000 : ℝ)^4515 := by
      have hnat : (50001740603982937199 : ℕ)^1024*1250000000000000^4515 ≤ 1250009869072487^4515*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001740603982937199 50000000000000000000 1250009869072487 1250000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250009869072487/1250000000000000 : ℝ)) (X := (50001740603982937199/50000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100058450190216344941/100000000000000000000 : ℝ) ≤ (5000662674136843/5000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (100058450190216344941/100000000000000000000 : ℝ)^1024 ≤ (5000662674136843/5000000000000000 : ℝ)^4515 := by
      have hnat : (100058450190216344941 : ℕ)^1024*5000000000000000^4515 ≤ 5000662674136843^4515*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100058450190216344941 100000000000000000000 5000662674136843 5000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000662674136843/5000000000000000 : ℝ)) (X := (100058450190216344941/100000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25028354793116703871/25000000000000000000 : ℝ) ≤ (2500642935991869/2500000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (25028354793116703871/25000000000000000000 : ℝ)^1024 ≤ (2500642935991869/2500000000000000 : ℝ)^4515 := by
      have hnat : (25028354793116703871 : ℕ)^1024*2500000000000000^4515 ≤ 2500642935991869^4515*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25028354793116703871 25000000000000000000 2500642935991869 2500000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500642935991869/2500000000000000 : ℝ)) (X := (25028354793116703871/25000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1740603982937199/100000000000000000000 : ℝ) ≤ ((5011501452007315179/5012500000000000000 : ℝ)+2*(124639569379/100250000000000 : ℝ)*(8329/100000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (5011501452007315179/5012500000000000000 : ℝ)+2*(124639569379/100250000000000 : ℝ)*(8329/100000 : ℝ)=(1250009869072487/1250000000000000 : ℝ) by norm_num, show 1+2*(1740603982937199/100000000000000000000 : ℝ)=(50001740603982937199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28354793116703871/50000000000000000000 : ℝ)+(1740603982937199/100000000000000000000 : ℝ) ≤ ((5011501452007315179/5012500000000000000 : ℝ)+(124639569379/100250000000000 : ℝ)*((9177/50000 : ℝ)+(8329/100000 : ℝ)))^(4515/1024 : ℝ) := by
    rw [show (5011501452007315179/5012500000000000000 : ℝ)+(124639569379/100250000000000 : ℝ)*((9177/50000 : ℝ)+(8329/100000 : ℝ))=(5000662674136843/5000000000000000 : ℝ) by norm_num, show 1+(28354793116703871/50000000000000000000 : ℝ)+(1740603982937199/100000000000000000000 : ℝ)=(100058450190216344941/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28354793116703871/50000000000000000000 : ℝ) ≤ ((5011501452007315179/5012500000000000000 : ℝ)+2*(124639569379/100250000000000 : ℝ)*(9177/50000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (5011501452007315179/5012500000000000000 : ℝ)+2*(124639569379/100250000000000 : ℝ)*(9177/50000 : ℝ)=(2500642935991869/2500000000000000 : ℝ) by norm_num, show 1+2*(28354793116703871/50000000000000000000 : ℝ)=(25028354793116703871/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5011501452007315179/5012500000000000000 : ℝ)*(X 1 0+X 2 0)+(124639569379/100250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (8329/100000 : ℝ)) (hi := (9177/50000 : ℝ)) (c := (5011501452007315179/5012500000000000000 : ℝ)) (alpha := (124639569379/100250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5011501452007315179/5012500000000000000 : ℝ)*(X 0 1+X 2 1)+(124639569379/100250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (8329/100000 : ℝ)) (hi := (9177/50000 : ℝ)) (c := (5011501452007315179/5012500000000000000 : ℝ)) (alpha := (124639569379/100250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5011501452007315179/5012500000000000000 : ℝ)*(X 0 2+X 1 2)+(124639569379/100250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (8329/100000 : ℝ)) (hi := (9177/50000 : ℝ)) (c := (5011501452007315179/5012500000000000000 : ℝ)) (alpha := (124639569379/100250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-466739013/2500000000 : ℝ)*X 0 0+(5458560387/10000000000 : ℝ)*X 0 1+(5195112249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358220029/10000000000 : ℝ)*X 1 0+(-2002590343/10000000000 : ℝ)*X 1 1+(5195112257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679109961/5000000000 : ℝ)*X 2 0+(5195112313/10000000000 : ℝ)*X 2 1+(-2002590411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4268102017/10000000000 : ℝ)*X 0 0+(397868231/1000000000 : ℝ)*X 0 1+(4575230829/10000000000 : ℝ)*X 0 2+(4268102017/10000000000 : ℝ)*X 1 0+(397868231/1000000000 : ℝ)*X 1 1+(4575230829/10000000000 : ℝ)*X 1 2+(4268102017/10000000000 : ℝ)*X 2 0+(397868231/1000000000 : ℝ)*X 2 1+(4575230829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1867007947/10000000000 : ℝ)*X 0 0+(2598382137/5000000000 : ℝ)*X 0 1+(1091378821/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057812703/2000000000 : ℝ)*X 1 0+(-1740808453/10000000000 : ℝ)*X 1 1+(5456895201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322266023/2500000000 : ℝ)*X 2 0+(5456894439/10000000000 : ℝ)*X 2 1+(-1740808719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4268221871/10000000000 : ℝ)*X 0 0+(4571492963/10000000000 : ℝ)*X 0 1+(796490621/2000000000 : ℝ)*X 0 2+(4268221871/10000000000 : ℝ)*X 1 0+(4571492963/10000000000 : ℝ)*X 1 1+(796490621/2000000000 : ℝ)*X 1 2+(4268221871/10000000000 : ℝ)*X 2 0+(4571492963/10000000000 : ℝ)*X 2 1+(796490621/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86707355690123333364642093/25062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (698988913/100000000000000 : ℝ)*(base19) + (574783829/100000000000000 : ℝ)*(base23) + (6484103/25000000000000 : ℝ)*(lower2) + (29708387/25000000000000 : ℝ)*(upper3) + (3085193/25000000000000 : ℝ)*(upper5) + (547214893613989/20000000000000 : ℝ)*(major0) + (547214893613989/20000000000000 : ℝ)*(major1) + (547214893613989/20000000000000 : ℝ)*(major2) + (1897912194410841/50000000000000 : ℝ)*(sp0) + (3795832096047281/100000000000000 : ℝ)*(sp1) + (948958055063091/25000000000000 : ℝ)*(sp2) + (1676312314008617/100000000000000 : ℝ)*(sp3) + (8406214513/100000000000000 : ℝ)*(sp4) + (742354713/20000000000000 : ℝ)*(sp7) + (1676316025782181/100000000000000 : ℝ)*(f.failure) + (1897916397518097/50000000000000 : ℝ)*(f.sum) + (4765541896017/2005000000000000000000000000 : ℝ)*base65 + (1242039635637260969/100250000000000000000000000000000 : ℝ)*base68 + (616874985547260969/100250000000000000000000000000000 : ℝ)*base70 + (553553100810260969/100250000000000000000000000000000 : ℝ)*base72 + (115824561453/125312500000000000000000000 : ℝ)*base74 + (675470562580760969/100250000000000000000000000000000 : ℝ)*base76 + (139240347825010969/100250000000000000000000000000000 : ℝ)*base78 + (1317028236153739031/100250000000000000000000000000000 : ℝ)*base79 + (12870593949/250625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (6609231/1000000000000000000000 : ℝ)*base90 + (6609231/1000000000000000000000 : ℝ)*base92 + (6609231/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49307077030648494066543/5012500000000000000000000000 : ℝ) := by norm_num
    linear_combination (122274409/20000000000000 : ℝ)*(base23) + (96089553/50000000000000 : ℝ)*(lower2) + (229480529/100000000000000 : ℝ)*(upper3) + (67825569/25000000000000 : ℝ)*(lower4) + (2770959273736439/100000000000000 : ℝ)*(major0) + (2770959273736439/100000000000000 : ℝ)*(major1) + (2770959273736439/100000000000000 : ℝ)*(major2) + (7328475727/100000000000000 : ℝ)*(sp1) + (5285496101/50000000000000 : ℝ)*(sp2) + (420075167/10000000000000 : ℝ)*(sp3) + (3844229252570927/100000000000000 : ℝ)*(sp4) + (4805277405119/125000000000 : ℝ)*(sp5) + (96105451755167/2500000000000 : ℝ)*(sp6) + (339536953251231/20000000000000 : ℝ)*(sp7) + (106105560437989/6250000000000 : ℝ)*(f.failure) + (3844229252570927/100000000000000 : ℝ)*(f.sum) + (24537120411347/2506250000000000000000000000 : ℝ)*base66 + (3665109112584592419/501250000000000000000000000000000 : ℝ)*base68 + (10636518756319157581/501250000000000000000000000000000 : ℝ)*base69 + (4790661734478342419/501250000000000000000000000000000 : ℝ)*base72 + (18601937431169/5012500000000000000000000000 : ℝ)*base74 + (625986984689157581/501250000000000000000000000000000 : ℝ)*base75 + (18211089881620407581/501250000000000000000000000000000 : ℝ)*base77 + (17111227453769592419/501250000000000000000000000000000 : ℝ)*base80 + (4176690978687/10025000000000000000000000000 : ℝ)*base81 + (254439/62500000000000000000 : ℝ)*base90 + (254439/62500000000000000000 : ℝ)*base92 + (254439/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1510_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9177/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8329/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2607/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4001/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1510_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1510_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2607/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4001/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1510_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1510_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1510_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2607/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4001/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1510_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

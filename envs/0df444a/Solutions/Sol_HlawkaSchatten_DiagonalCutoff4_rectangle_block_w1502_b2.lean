-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1502_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:53:01.574995+00:00
-- url     : https://prove2.me/submissions/73bdad12-2de5-46c6-b9f5-afa5b98730fe

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
theorem support_rectangle_w1502_s6_0 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1882892767/10000000000 : ℝ)*x 0 + (5434534687/10000000000 : ℝ)*x 1 + (1043423489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1882892767/10000000000 : ℝ)^4501 ≤ (11514811193523/100000000000000 : ℝ)^3477 := by
    have hnat : (1882892767 : ℕ)^4501*100000000000000^3477 ≤ 11514811193523^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882892767 10000000000 11514811193523 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434534687/10000000000 : ℝ)^4501 ≤ (45411504620081/100000000000000 : ℝ)^3477 := by
    have hnat : (5434534687 : ℕ)^4501*100000000000000^3477 ≤ 45411504620081^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434534687 10000000000 45411504620081 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043423489/2000000000 : ℝ)^4501 ≤ (21536842082771/50000000000000 : ℝ)^3477 := by
    have hnat : (1043423489 : ℕ)^4501*50000000000000^3477 ≤ 21536842082771^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043423489 2000000000 21536842082771 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1882892767/10000000000 : ℝ), (5434534687/10000000000 : ℝ), (1043423489/2000000000 : ℝ)] ![(11514811193523/100000000000000 : ℝ), (45411504620081/100000000000000 : ℝ), (21536842082771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1882892767/10000000000 : ℝ)|^4501 ≤ (11514811193523/100000000000000 : ℝ)^3477
        have hw : |(-1882892767/10000000000 : ℝ)|=(1882892767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434534687/10000000000 : ℝ)|^4501 ≤ (45411504620081/100000000000000 : ℝ)^3477
        have hw : |(5434534687/10000000000 : ℝ)|=(5434534687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043423489/2000000000 : ℝ)|^4501 ≤ (21536842082771/50000000000000 : ℝ)^3477
        have hw : |(1043423489/2000000000 : ℝ)|=(1043423489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s6_1 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352140301/10000000000 : ℝ)*x 0 + (-199426607/1000000000 : ℝ)*x 1 + (5217117293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352140301/10000000000 : ℝ)^4501 ≤ (11130559845049/25000000000000 : ℝ)^3477 := by
    have hnat : (5352140301 : ℕ)^4501*25000000000000^3477 ≤ 11130559845049^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352140301 10000000000 11130559845049 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199426607/1000000000 : ℝ)^4501 ≤ (12404078065373/100000000000000 : ℝ)^3477 := by
    have hnat : (199426607 : ℕ)^4501*100000000000000^3477 ≤ 12404078065373^3477*1000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199426607 1000000000 12404078065373 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217117293/10000000000 : ℝ)^4501 ≤ (21536841270503/50000000000000 : ℝ)^3477 := by
    have hnat : (5217117293 : ℕ)^4501*50000000000000^3477 ≤ 21536841270503^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217117293 10000000000 21536841270503 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352140301/10000000000 : ℝ), (-199426607/1000000000 : ℝ), (5217117293/10000000000 : ℝ)] ![(11130559845049/25000000000000 : ℝ), (12404078065373/100000000000000 : ℝ), (21536841270503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352140301/10000000000 : ℝ)|^4501 ≤ (11130559845049/25000000000000 : ℝ)^3477
        have hw : |(5352140301/10000000000 : ℝ)|=(5352140301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199426607/1000000000 : ℝ)|^4501 ≤ (12404078065373/100000000000000 : ℝ)^3477
        have hw : |(-199426607/1000000000 : ℝ)|=(199426607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217117293/10000000000 : ℝ)|^4501 ≤ (21536841270503/50000000000000 : ℝ)^3477
        have hw : |(5217117293/10000000000 : ℝ)|=(5217117293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s6_2 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352140101/10000000000 : ℝ)*x 0 + (1304279369/2500000000 : ℝ)*x 1 + (-997133047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352140101/10000000000 : ℝ)^4501 ≤ (44522237226503/100000000000000 : ℝ)^3477 := by
    have hnat : (5352140101 : ℕ)^4501*100000000000000^3477 ≤ 44522237226503^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352140101 10000000000 44522237226503 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304279369/2500000000 : ℝ)^4501 ≤ (21536842248431/50000000000000 : ℝ)^3477 := by
    have hnat : (1304279369 : ℕ)^4501*50000000000000^3477 ≤ 21536842248431^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304279369 2500000000 21536842248431 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (997133047/5000000000 : ℝ)^4501 ≤ (12404078258613/100000000000000 : ℝ)^3477 := by
    have hnat : (997133047 : ℕ)^4501*100000000000000^3477 ≤ 12404078258613^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997133047 5000000000 12404078258613 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352140101/10000000000 : ℝ), (1304279369/2500000000 : ℝ), (-997133047/5000000000 : ℝ)] ![(44522237226503/100000000000000 : ℝ), (21536842248431/50000000000000 : ℝ), (12404078258613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352140101/10000000000 : ℝ)|^4501 ≤ (44522237226503/100000000000000 : ℝ)^3477
        have hw : |(5352140101/10000000000 : ℝ)|=(5352140101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304279369/2500000000 : ℝ)|^4501 ≤ (21536842248431/50000000000000 : ℝ)^3477
        have hw : |(1304279369/2500000000 : ℝ)|=(1304279369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-997133047/5000000000 : ℝ)|^4501 ≤ (12404078258613/100000000000000 : ℝ)^3477
        have hw : |(-997133047/5000000000 : ℝ)|=(997133047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s6_3 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4274451961/10000000000 : ℝ)*x 0 + (201784111/500000000 : ℝ)*x 1 + (226261109/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274451961/10000000000 : ℝ)^4501 ≤ (33279150791329/100000000000000 : ℝ)^3477 := by
    have hnat : (4274451961 : ℕ)^4501*100000000000000^3477 ≤ 33279150791329^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274451961 10000000000 33279150791329 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201784111/500000000 : ℝ)^4501 ≤ (15446384717047/50000000000000 : ℝ)^3477 := by
    have hnat : (201784111 : ℕ)^4501*50000000000000^3477 ≤ 15446384717047^3477*500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201784111 500000000 15446384717047 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226261109/500000000 : ℝ)^4501 ≤ (447850996971/1250000000000 : ℝ)^3477 := by
    have hnat : (226261109 : ℕ)^4501*1250000000000^3477 ≤ 447850996971^3477*500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226261109 500000000 447850996971 1250000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274451961/10000000000 : ℝ), (201784111/500000000 : ℝ), (226261109/500000000 : ℝ)] ![(33279150791329/100000000000000 : ℝ), (15446384717047/50000000000000 : ℝ), (447850996971/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274451961/10000000000 : ℝ)|^4501 ≤ (33279150791329/100000000000000 : ℝ)^3477
        have hw : |(4274451961/10000000000 : ℝ)|=(4274451961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201784111/500000000 : ℝ)|^4501 ≤ (15446384717047/50000000000000 : ℝ)^3477
        have hw : |(201784111/500000000 : ℝ)|=(201784111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226261109/500000000 : ℝ)|^4501 ≤ (447850996971/1250000000000 : ℝ)^3477
        have hw : |(226261109/500000000 : ℝ)|=(226261109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s6_4 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1882922391/10000000000 : ℝ)*x 0 + (2609117123/5000000000 : ℝ)*x 1 + (1086681897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1882922391/10000000000 : ℝ)^4501 ≤ (5757522856863/50000000000000 : ℝ)^3477 := by
    have hnat : (1882922391 : ℕ)^4501*50000000000000^3477 ≤ 5757522856863^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882922391 10000000000 5757522856863 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609117123/5000000000 : ℝ)^4501 ≤ (43085620616309/100000000000000 : ℝ)^3477 := by
    have hnat : (2609117123 : ℕ)^4501*100000000000000^3477 ≤ 43085620616309^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609117123 5000000000 43085620616309 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086681897/2000000000 : ℝ)^4501 ≤ (11349833413147/25000000000000 : ℝ)^3477 := by
    have hnat : (1086681897 : ℕ)^4501*25000000000000^3477 ≤ 11349833413147^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086681897 2000000000 11349833413147 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1882922391/10000000000 : ℝ), (2609117123/5000000000 : ℝ), (1086681897/2000000000 : ℝ)] ![(5757522856863/50000000000000 : ℝ), (43085620616309/100000000000000 : ℝ), (11349833413147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1882922391/10000000000 : ℝ)|^4501 ≤ (5757522856863/50000000000000 : ℝ)^3477
        have hw : |(-1882922391/10000000000 : ℝ)|=(1882922391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609117123/5000000000 : ℝ)|^4501 ≤ (43085620616309/100000000000000 : ℝ)^3477
        have hw : |(2609117123/5000000000 : ℝ)|=(2609117123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086681897/2000000000 : ℝ)|^4501 ≤ (11349833413147/25000000000000 : ℝ)^3477
        have hw : |(1086681897/2000000000 : ℝ)|=(1086681897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s6_5 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059030659/2000000000 : ℝ)*x 0 + (-1777973937/10000000000 : ℝ)*x 1 + (271670481/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059030659/2000000000 : ℝ)^4501 ≤ (21954770663149/50000000000000 : ℝ)^3477 := by
    have hnat : (1059030659 : ℕ)^4501*50000000000000^3477 ≤ 21954770663149^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059030659 2000000000 21954770663149 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1777973937/10000000000 : ℝ)^4501 ≤ (10691123549279/100000000000000 : ℝ)^3477 := by
    have hnat : (1777973937 : ℕ)^4501*100000000000000^3477 ≤ 10691123549279^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777973937 10000000000 10691123549279 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271670481/500000000 : ℝ)^4501 ≤ (45399335112797/100000000000000 : ℝ)^3477 := by
    have hnat : (271670481 : ℕ)^4501*100000000000000^3477 ≤ 45399335112797^3477*500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271670481 500000000 45399335112797 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059030659/2000000000 : ℝ), (-1777973937/10000000000 : ℝ), (271670481/500000000 : ℝ)] ![(21954770663149/50000000000000 : ℝ), (10691123549279/100000000000000 : ℝ), (45399335112797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059030659/2000000000 : ℝ)|^4501 ≤ (21954770663149/50000000000000 : ℝ)^3477
        have hw : |(1059030659/2000000000 : ℝ)|=(1059030659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1777973937/10000000000 : ℝ)|^4501 ≤ (10691123549279/100000000000000 : ℝ)^3477
        have hw : |(-1777973937/10000000000 : ℝ)|=(1777973937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271670481/500000000 : ℝ)|^4501 ≤ (45399335112797/100000000000000 : ℝ)^3477
        have hw : |(271670481/500000000 : ℝ)|=(271670481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s6_6 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661894187/1250000000 : ℝ)*x 0 + (5433409559/10000000000 : ℝ)*x 1 + (-1777973743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661894187/1250000000 : ℝ)^4501 ≤ (43909543483947/100000000000000 : ℝ)^3477 := by
    have hnat : (661894187 : ℕ)^4501*100000000000000^3477 ≤ 43909543483947^3477*1250000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661894187 1250000000 43909543483947 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433409559/10000000000 : ℝ)^4501 ≤ (45399334452999/100000000000000 : ℝ)^3477 := by
    have hnat : (5433409559 : ℕ)^4501*100000000000000^3477 ≤ 45399334452999^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433409559 10000000000 45399334452999 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1777973743/10000000000 : ℝ)^4501 ≤ (2138224407837/20000000000000 : ℝ)^3477 := by
    have hnat : (1777973743 : ℕ)^4501*20000000000000^3477 ≤ 2138224407837^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777973743 10000000000 2138224407837 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661894187/1250000000 : ℝ), (5433409559/10000000000 : ℝ), (-1777973743/10000000000 : ℝ)] ![(43909543483947/100000000000000 : ℝ), (45399334452999/100000000000000 : ℝ), (2138224407837/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661894187/1250000000 : ℝ)|^4501 ≤ (43909543483947/100000000000000 : ℝ)^3477
        have hw : |(661894187/1250000000 : ℝ)|=(661894187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433409559/10000000000 : ℝ)|^4501 ≤ (45399334452999/100000000000000 : ℝ)^3477
        have hw : |(5433409559/10000000000 : ℝ)|=(5433409559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1777973743/10000000000 : ℝ)|^4501 ≤ (2138224407837/20000000000000 : ℝ)^3477
        have hw : |(-1777973743/10000000000 : ℝ)|=(1777973743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s6_7 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534314943/1250000000 : ℝ)*x 0 + (90454131/200000000 : ℝ)*x 1 + (504776867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534314943/1250000000 : ℝ)^4501 ≤ (831995798213/2500000000000 : ℝ)^3477 := by
    have hnat : (534314943 : ℕ)^4501*2500000000000^3477 ≤ 831995798213^3477*1250000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534314943 1250000000 831995798213 2500000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90454131/200000000 : ℝ)^4501 ≤ (17901149396757/50000000000000 : ℝ)^3477 := by
    have hnat : (90454131 : ℕ)^4501*50000000000000^3477 ≤ 17901149396757^3477*200000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90454131 200000000 17901149396757 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504776867/1250000000 : ℝ)^4501 ≤ (7729467316669/25000000000000 : ℝ)^3477 := by
    have hnat : (504776867 : ℕ)^4501*25000000000000^3477 ≤ 7729467316669^3477*1250000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504776867 1250000000 7729467316669 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534314943/1250000000 : ℝ), (90454131/200000000 : ℝ), (504776867/1250000000 : ℝ)] ![(831995798213/2500000000000 : ℝ), (17901149396757/50000000000000 : ℝ), (7729467316669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534314943/1250000000 : ℝ)|^4501 ≤ (831995798213/2500000000000 : ℝ)^3477
        have hw : |(534314943/1250000000 : ℝ)|=(534314943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90454131/200000000 : ℝ)|^4501 ≤ (17901149396757/50000000000000 : ℝ)^3477
        have hw : |(90454131/200000000 : ℝ)|=(90454131/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504776867/1250000000 : ℝ)|^4501 ≤ (7729467316669/25000000000000 : ℝ)^3477
        have hw : |(504776867/1250000000 : ℝ)|=(504776867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1502_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10877/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2719/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2719/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2719/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2719/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2719/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2719/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2719/25000 : ℝ) ^ (4499/1024 : ℝ) ≤ (5843522658100303/100000000000000000000 : ℝ) := by
    have hpowers : (2719/25000 : ℝ)^4499 ≤ (5843522658100303/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2719 : ℕ)^4499*100000000000000000000^1024 ≤ 5843522658100303^1024*25000^4499 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2719 25000 5843522658100303 100000000000000000000 4499 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2719/25000 : ℝ)) (X := (5843522658100303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4499/1024 : ℝ) ≤ (27563708309205727/100000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4499 ≤ (27563708309205727/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4499*100000000000000000000^1024 ≤ 27563708309205727^1024*100000^4499 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 27563708309205727 100000000000000000000 4499 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (27563708309205727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005843522658100303/50000000000000000000 : ℝ) ≤ (5000132996157883/5000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (50005843522658100303/50000000000000000000 : ℝ)^1024 ≤ (5000132996157883/5000000000000000 : ℝ)^4499 := by
      have hnat : (50005843522658100303 : ℕ)^1024*5000000000000000^4499 ≤ 5000132996157883^4499*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005843522658100303 50000000000000000000 5000132996157883 5000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000132996157883/5000000000000000 : ℝ)) (X := (50005843522658100303/50000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003340723096730603/10000000000000000000 : ℝ) ≤ (10000760270989427/10000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (10003340723096730603/10000000000000000000 : ℝ)^1024 ≤ (10000760270989427/10000000000000000 : ℝ)^4499 := by
      have hnat : (10003340723096730603 : ℕ)^1024*10000000000000000^4499 ≤ 10000760270989427^4499*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003340723096730603 10000000000000000000 10000760270989427 10000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000760270989427/10000000000000000 : ℝ)) (X := (10003340723096730603/10000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027563708309205727/50000000000000000000 : ℝ) ≤ (625078409353943/625000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (50027563708309205727/50000000000000000000 : ℝ)^1024 ≤ (625078409353943/625000000000000 : ℝ)^4499 := by
      have hnat : (50027563708309205727 : ℕ)^1024*625000000000000^4499 ≤ 625078409353943^4499*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027563708309205727 50000000000000000000 625078409353943 625000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625078409353943/625000000000000 : ℝ)) (X := (50027563708309205727/50000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5843522658100303/100000000000000000000 : ℝ) ≤ ((7673412224150771393/7675000000000000000 : ℝ)+2*(164759557887/153500000000000 : ℝ)*(2719/25000 : ℝ))^(4499/1024 : ℝ) := by
    rw [show (7673412224150771393/7675000000000000000 : ℝ)+2*(164759557887/153500000000000 : ℝ)*(2719/25000 : ℝ)=(5000132996157883/5000000000000000 : ℝ) by norm_num, show 1+2*(5843522658100303/100000000000000000000 : ℝ)=(50005843522658100303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27563708309205727/100000000000000000000 : ℝ)+(5843522658100303/100000000000000000000 : ℝ) ≤ ((7673412224150771393/7675000000000000000 : ℝ)+(164759557887/153500000000000 : ℝ)*((15481/100000 : ℝ)+(2719/25000 : ℝ)))^(4499/1024 : ℝ) := by
    rw [show (7673412224150771393/7675000000000000000 : ℝ)+(164759557887/153500000000000 : ℝ)*((15481/100000 : ℝ)+(2719/25000 : ℝ))=(10000760270989427/10000000000000000 : ℝ) by norm_num, show 1+(27563708309205727/100000000000000000000 : ℝ)+(5843522658100303/100000000000000000000 : ℝ)=(10003340723096730603/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27563708309205727/100000000000000000000 : ℝ) ≤ ((7673412224150771393/7675000000000000000 : ℝ)+2*(164759557887/153500000000000 : ℝ)*(15481/100000 : ℝ))^(4499/1024 : ℝ) := by
    rw [show (7673412224150771393/7675000000000000000 : ℝ)+2*(164759557887/153500000000000 : ℝ)*(15481/100000 : ℝ)=(625078409353943/625000000000000 : ℝ) by norm_num, show 1+2*(27563708309205727/100000000000000000000 : ℝ)=(50027563708309205727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7673412224150771393/7675000000000000000 : ℝ)*(X 1 0+X 2 0)+(164759557887/153500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (7673412224150771393/7675000000000000000 : ℝ)) (alpha := (164759557887/153500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7673412224150771393/7675000000000000000 : ℝ)*(X 0 1+X 2 1)+(164759557887/153500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (7673412224150771393/7675000000000000000 : ℝ)) (alpha := (164759557887/153500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7673412224150771393/7675000000000000000 : ℝ)*(X 0 2+X 1 2)+(164759557887/153500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (7673412224150771393/7675000000000000000 : ℝ)) (alpha := (164759557887/153500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1882892767/10000000000 : ℝ)*X 0 0+(5434534687/10000000000 : ℝ)*X 0 1+(1043423489/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352140301/10000000000 : ℝ)*X 1 0+(-199426607/1000000000 : ℝ)*X 1 1+(5217117293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352140101/10000000000 : ℝ)*X 2 0+(1304279369/2500000000 : ℝ)*X 2 1+(-997133047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4274451961/10000000000 : ℝ)*X 0 0+(201784111/500000000 : ℝ)*X 0 1+(226261109/500000000 : ℝ)*X 0 2+(4274451961/10000000000 : ℝ)*X 1 0+(201784111/500000000 : ℝ)*X 1 1+(226261109/500000000 : ℝ)*X 1 2+(4274451961/10000000000 : ℝ)*X 2 0+(201784111/500000000 : ℝ)*X 2 1+(226261109/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1882922391/10000000000 : ℝ)*X 0 0+(2609117123/5000000000 : ℝ)*X 0 1+(1086681897/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1059030659/2000000000 : ℝ)*X 1 0+(-1777973937/10000000000 : ℝ)*X 1 1+(271670481/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661894187/1250000000 : ℝ)*X 2 0+(5433409559/10000000000 : ℝ)*X 2 1+(-1777973743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((534314943/1250000000 : ℝ)*X 0 0+(90454131/200000000 : ℝ)*X 0 1+(504776867/1250000000 : ℝ)*X 0 2+(534314943/1250000000 : ℝ)*X 1 0+(90454131/200000000 : ℝ)*X 1 1+(504776867/1250000000 : ℝ)*X 1 2+(534314943/1250000000 : ℝ)*X 2 0+(90454131/200000000 : ℝ)*X 2 1+(504776867/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (392904148527668321495432841/95937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53460511/6250000000000 : ℝ)*(base19) + (595719383/100000000000000 : ℝ)*(base23) + (64631713/50000000000000 : ℝ)*(upper3) + (11744553/25000000000000 : ℝ)*(upper4) + (202449/1250000000000 : ℝ)*(upper5) + (1660554447246379/50000000000000 : ℝ)*(major0) + (1660554447246379/50000000000000 : ℝ)*(major1) + (3321108894492759/100000000000000 : ℝ)*(major2) + (574933023849393/12500000000000 : ℝ)*(sp0) + (287467065100979/6250000000000 : ℝ)*(sp1) + (4599473301264457/100000000000000 : ℝ)*(sp2) + (408547683610459/20000000000000 : ℝ)*(sp3) + (1941237739/20000000000000 : ℝ)*(sp4) + (1334358861/25000000000000 : ℝ)*(sp7) + (1021371877743869/50000000000000 : ℝ)*(f.failure) + (4599473896983839/100000000000000 : ℝ)*(f.sum) + (59948560140721/15350000000000000000000000000 : ℝ)*base66 + (2754583393150639053/383750000000000000000000000000000 : ℝ)*base68 + (4336097471987643287/767500000000000000000000000000000 : ℝ)*base69 + (5175520499874389053/383750000000000000000000000000000 : ℝ)*base72 + (50281249594421/15350000000000000000000000000 : ℝ)*base74 + (8341174647709856713/767500000000000000000000000000000 : ℝ)*base76 + (907893857510314053/383750000000000000000000000000000 : ℝ)*base78 + (2354284234145314053/383750000000000000000000000000000 : ℝ)*base80 + (732116794853/239843750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3952807/1250000000000000000000 : ℝ)*base90 + (3952807/1250000000000000000000 : ℝ)*base92 + (16452807/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73148960114051804665909491/23984375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119563279/10000000000000 : ℝ)*(base19) + (421847321/25000000000000 : ℝ)*(base23) + (191574889/50000000000000 : ℝ)*(lower1) + (225586083/100000000000000 : ℝ)*(upper3) + (25512577/20000000000000 : ℝ)*(lower4) + (2323599/781250000000 : ℝ)*(upper5) + (209730273287271/6250000000000 : ℝ)*(major0) + (209730273287271/6250000000000 : ℝ)*(major1) + (209730273287271/6250000000000 : ℝ)*(major2) + (864629733/12500000000000 : ℝ)*(sp2) + (4647358243607961/100000000000000 : ℝ)*(sp4) + (4647357047975171/100000000000000 : ℝ)*(sp5) + (4647349639180813/100000000000000 : ℝ)*(sp6) + (129000649995171/6250000000000 : ℝ)*(sp7) + (129000649995171/6250000000000 : ℝ)*(f.failure) + (4647358243607961/100000000000000 : ℝ)*(f.sum) + (48051084268757/7675000000000000000000000000 : ℝ)*base65 + (563229505368623997/47968750000000000000000000000000 : ℝ)*base68 + (17881115736844753/47968750000000000000000000000000 : ℝ)*base69 + (191014924278094753/47968750000000000000000000000000 : ℝ)*base71 + (383156354257/7675000000000000000000000000 : ℝ)*base73 + (2430055189948563503/47968750000000000000000000000000 : ℝ)*base75 + (57469057626688503/47968750000000000000000000000000 : ℝ)*base77 + (564345753770967747/47968750000000000000000000000000 : ℝ)*base80 + (14287139935857/7675000000000000000000000000 : ℝ)*base81 + (656313/156250000000000000000 : ℝ)*base90 + (656313/156250000000000000000 : ℝ)*base92 + (656313/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1502_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10877/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1502_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1502_box_0 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1667463033/10000000000 : ℝ)*x 0 + (675489263/1250000000 : ℝ)*x 1 + (675489129/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1667463033/10000000000 : ℝ)^4501 ≤ (9838899214287/100000000000000 : ℝ)^3477 := by
    have hnat : (1667463033 : ℕ)^4501*100000000000000^3477 ≤ 9838899214287^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667463033 10000000000 9838899214287 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675489263/1250000000 : ℝ)^4501 ≤ (4508055617479/10000000000000 : ℝ)^3477 := by
    have hnat : (675489263 : ℕ)^4501*10000000000000^3477 ≤ 4508055617479^3477*1250000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675489263 1250000000 4508055617479 10000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675489129/1250000000 : ℝ)^4501 ≤ (45080544598219/100000000000000 : ℝ)^3477 := by
    have hnat : (675489129 : ℕ)^4501*100000000000000^3477 ≤ 45080544598219^3477*1250000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675489129 1250000000 45080544598219 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1667463033/10000000000 : ℝ), (675489263/1250000000 : ℝ), (675489129/1250000000 : ℝ)] ![(9838899214287/100000000000000 : ℝ), (4508055617479/10000000000000 : ℝ), (45080544598219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1667463033/10000000000 : ℝ)|^4501 ≤ (9838899214287/100000000000000 : ℝ)^3477
        have hw : |(-1667463033/10000000000 : ℝ)|=(1667463033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675489263/1250000000 : ℝ)|^4501 ≤ (4508055617479/10000000000000 : ℝ)^3477
        have hw : |(675489263/1250000000 : ℝ)|=(675489263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675489129/1250000000 : ℝ)|^4501 ≤ (45080544598219/100000000000000 : ℝ)^3477
        have hw : |(675489129/1250000000 : ℝ)|=(675489129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_1 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270636333/10000000000 : ℝ)*x 0 + (-1852263283/10000000000 : ℝ)*x 1 + (1350978231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270636333/10000000000 : ℝ)^4501 ≤ (43646541891309/100000000000000 : ℝ)^3477 := by
    have hnat : (5270636333 : ℕ)^4501*100000000000000^3477 ≤ 43646541891309^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270636333 10000000000 43646541891309 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1852263283/10000000000 : ℝ)^4501 ≤ (5636457325867/50000000000000 : ℝ)^3477 := by
    have hnat : (1852263283 : ℕ)^4501*50000000000000^3477 ≤ 5636457325867^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852263283 10000000000 5636457325867 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350978231/2500000000 : ℝ)^4501 ≤ (45080543431923/100000000000000 : ℝ)^3477 := by
    have hnat : (1350978231 : ℕ)^4501*100000000000000^3477 ≤ 45080543431923^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350978231 2500000000 45080543431923 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270636333/10000000000 : ℝ), (-1852263283/10000000000 : ℝ), (1350978231/2500000000 : ℝ)] ![(43646541891309/100000000000000 : ℝ), (5636457325867/50000000000000 : ℝ), (45080543431923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270636333/10000000000 : ℝ)|^4501 ≤ (43646541891309/100000000000000 : ℝ)^3477
        have hw : |(5270636333/10000000000 : ℝ)|=(5270636333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1852263283/10000000000 : ℝ)|^4501 ≤ (5636457325867/50000000000000 : ℝ)^3477
        have hw : |(-1852263283/10000000000 : ℝ)|=(1852263283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350978231/2500000000 : ℝ)|^4501 ≤ (45080543431923/100000000000000 : ℝ)^3477
        have hw : |(1350978231/2500000000 : ℝ)|=(1350978231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_2 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270637641/10000000000 : ℝ)*x 0 + (5403912527/10000000000 : ℝ)*x 1 + (-37045241/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270637641/10000000000 : ℝ)^4501 ≤ (43646555912951/100000000000000 : ℝ)^3477 := by
    have hnat : (5270637641 : ℕ)^4501*100000000000000^3477 ≤ 43646555912951^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270637641 10000000000 43646555912951 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403912527/10000000000 : ℝ)^4501 ≤ (9016107828941/20000000000000 : ℝ)^3477 := by
    have hnat : (5403912527 : ℕ)^4501*20000000000000^3477 ≤ 9016107828941^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403912527 10000000000 9016107828941 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37045241/200000000 : ℝ)^4501 ≤ (1409113117209/12500000000000 : ℝ)^3477 := by
    have hnat : (37045241 : ℕ)^4501*12500000000000^3477 ≤ 1409113117209^3477*200000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37045241 200000000 1409113117209 12500000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270637641/10000000000 : ℝ), (5403912527/10000000000 : ℝ), (-37045241/200000000 : ℝ)] ![(43646555912951/100000000000000 : ℝ), (9016107828941/20000000000000 : ℝ), (1409113117209/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270637641/10000000000 : ℝ)|^4501 ≤ (43646555912951/100000000000000 : ℝ)^3477
        have hw : |(5270637641/10000000000 : ℝ)|=(5270637641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403912527/10000000000 : ℝ)|^4501 ≤ (9016107828941/20000000000000 : ℝ)^3477
        have hw : |(5403912527/10000000000 : ℝ)|=(5403912527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37045241/200000000 : ℝ)|^4501 ≤ (1409113117209/12500000000000 : ℝ)^3477
        have hw : |(-37045241/200000000 : ℝ)|=(37045241/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_3 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2238988033/5000000000 : ℝ)*x 0 + (4179736613/10000000000 : ℝ)*x 1 + (261233669/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238988033/5000000000 : ℝ)^4501 ≤ (8836148360491/25000000000000 : ℝ)^3477 := by
    have hnat : (2238988033 : ℕ)^4501*25000000000000^3477 ≤ 8836148360491^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238988033 5000000000 8836148360491 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4179736613/10000000000 : ℝ)^4501 ≤ (16163846402067/50000000000000 : ℝ)^3477 := by
    have hnat : (4179736613 : ℕ)^4501*50000000000000^3477 ≤ 16163846402067^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4179736613 10000000000 16163846402067 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261233669/625000000 : ℝ)^4501 ≤ (16163856869837/50000000000000 : ℝ)^3477 := by
    have hnat : (261233669 : ℕ)^4501*50000000000000^3477 ≤ 16163856869837^3477*625000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261233669 625000000 16163856869837 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2238988033/5000000000 : ℝ), (4179736613/10000000000 : ℝ), (261233669/625000000 : ℝ)] ![(8836148360491/25000000000000 : ℝ), (16163846402067/50000000000000 : ℝ), (16163856869837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2238988033/5000000000 : ℝ)|^4501 ≤ (8836148360491/25000000000000 : ℝ)^3477
        have hw : |(2238988033/5000000000 : ℝ)|=(2238988033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4179736613/10000000000 : ℝ)|^4501 ≤ (16163846402067/50000000000000 : ℝ)^3477
        have hw : |(4179736613/10000000000 : ℝ)|=(4179736613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261233669/625000000 : ℝ)|^4501 ≤ (16163856869837/50000000000000 : ℝ)^3477
        have hw : |(261233669/625000000 : ℝ)|=(261233669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_4 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-262971243/1250000000 : ℝ)*x 0 + (5243288243/10000000000 : ℝ)*x 1 + (1048657651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262971243/1250000000 : ℝ)^4501 ≤ (13292805616379/100000000000000 : ℝ)^3477 := by
    have hnat : (262971243 : ℕ)^4501*100000000000000^3477 ≤ 13292805616379^3477*1250000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262971243 1250000000 13292805616379 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243288243/10000000000 : ℝ)^4501 ≤ (43353597120409/100000000000000 : ℝ)^3477 := by
    have hnat : (5243288243 : ℕ)^4501*100000000000000^3477 ≤ 43353597120409^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243288243 10000000000 43353597120409 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048657651/2000000000 : ℝ)^4501 ≤ (43353597248851/100000000000000 : ℝ)^3477 := by
    have hnat : (1048657651 : ℕ)^4501*100000000000000^3477 ≤ 43353597248851^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048657651 2000000000 43353597248851 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262971243/1250000000 : ℝ), (5243288243/10000000000 : ℝ), (1048657651/2000000000 : ℝ)] ![(13292805616379/100000000000000 : ℝ), (43353597120409/100000000000000 : ℝ), (43353597248851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262971243/1250000000 : ℝ)|^4501 ≤ (13292805616379/100000000000000 : ℝ)^3477
        have hw : |(-262971243/1250000000 : ℝ)|=(262971243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243288243/10000000000 : ℝ)|^4501 ≤ (43353597120409/100000000000000 : ℝ)^3477
        have hw : |(5243288243/10000000000 : ℝ)|=(5243288243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048657651/2000000000 : ℝ)|^4501 ≤ (43353597248851/100000000000000 : ℝ)^3477
        have hw : |(1048657651/2000000000 : ℝ)|=(1048657651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_5 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076510723/2000000000 : ℝ)*x 0 + (-1918362299/10000000000 : ℝ)*x 1 + (5243288461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076510723/2000000000 : ℝ)^4501 ≤ (22425008894903/50000000000000 : ℝ)^3477 := by
    have hnat : (1076510723 : ℕ)^4501*50000000000000^3477 ≤ 22425008894903^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076510723 2000000000 22425008894903 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1918362299/10000000000 : ℝ)^4501 ≤ (5898191370813/50000000000000 : ℝ)^3477 := by
    have hnat : (1918362299 : ℕ)^4501*50000000000000^3477 ≤ 5898191370813^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918362299 10000000000 5898191370813 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243288461/10000000000 : ℝ)^4501 ≤ (43353599453771/100000000000000 : ℝ)^3477 := by
    have hnat : (5243288461 : ℕ)^4501*100000000000000^3477 ≤ 43353599453771^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243288461 10000000000 43353599453771 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076510723/2000000000 : ℝ), (-1918362299/10000000000 : ℝ), (5243288461/10000000000 : ℝ)] ![(22425008894903/50000000000000 : ℝ), (5898191370813/50000000000000 : ℝ), (43353599453771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076510723/2000000000 : ℝ)|^4501 ≤ (22425008894903/50000000000000 : ℝ)^3477
        have hw : |(1076510723/2000000000 : ℝ)|=(1076510723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1918362299/10000000000 : ℝ)|^4501 ≤ (5898191370813/50000000000000 : ℝ)^3477
        have hw : |(-1918362299/10000000000 : ℝ)|=(1918362299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243288461/10000000000 : ℝ)|^4501 ≤ (43353599453771/100000000000000 : ℝ)^3477
        have hw : |(5243288461/10000000000 : ℝ)|=(5243288461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_6 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691276957/5000000000 : ℝ)*x 0 + (5243287989/10000000000 : ℝ)*x 1 + (-1918362529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691276957/5000000000 : ℝ)^4501 ≤ (8970004202991/20000000000000 : ℝ)^3477 := by
    have hnat : (2691276957 : ℕ)^4501*20000000000000^3477 ≤ 8970004202991^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691276957 5000000000 8970004202991 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243287989/10000000000 : ℝ)^4501 ≤ (1083839860043/2500000000000 : ℝ)^3477 := by
    have hnat : (5243287989 : ℕ)^4501*2500000000000^3477 ≤ 1083839860043^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243287989 10000000000 1083839860043 2500000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918362529/10000000000 : ℝ)^4501 ≤ (5898192286233/50000000000000 : ℝ)^3477 := by
    have hnat : (1918362529 : ℕ)^4501*50000000000000^3477 ≤ 5898192286233^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918362529 10000000000 5898192286233 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691276957/5000000000 : ℝ), (5243287989/10000000000 : ℝ), (-1918362529/10000000000 : ℝ)] ![(8970004202991/20000000000000 : ℝ), (1083839860043/2500000000000 : ℝ), (5898192286233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691276957/5000000000 : ℝ)|^4501 ≤ (8970004202991/20000000000000 : ℝ)^3477
        have hw : |(2691276957/5000000000 : ℝ)|=(2691276957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243287989/10000000000 : ℝ)|^4501 ≤ (1083839860043/2500000000000 : ℝ)^3477
        have hw : |(5243287989/10000000000 : ℝ)|=(5243287989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1918362529/10000000000 : ℝ)|^4501 ≤ (5898192286233/50000000000000 : ℝ)^3477
        have hw : |(-1918362529/10000000000 : ℝ)|=(1918362529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_7 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2034279673/5000000000 : ℝ)*x 0 + (4384310733/10000000000 : ℝ)*x 1 + (137009691/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2034279673/5000000000 : ℝ)^4501 ≤ (15609474868153/50000000000000 : ℝ)^3477 := by
    have hnat : (2034279673 : ℕ)^4501*50000000000000^3477 ≤ 15609474868153^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034279673 5000000000 15609474868153 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4384310733/10000000000 : ℝ)^4501 ≤ (6878105655359/20000000000000 : ℝ)^3477 := by
    have hnat : (4384310733 : ℕ)^4501*20000000000000^3477 ≤ 6878105655359^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384310733 10000000000 6878105655359 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137009691/312500000 : ℝ)^4501 ≤ (34390521971093/100000000000000 : ℝ)^3477 := by
    have hnat : (137009691 : ℕ)^4501*100000000000000^3477 ≤ 34390521971093^3477*312500000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137009691 312500000 34390521971093 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2034279673/5000000000 : ℝ), (4384310733/10000000000 : ℝ), (137009691/312500000 : ℝ)] ![(15609474868153/50000000000000 : ℝ), (6878105655359/20000000000000 : ℝ), (34390521971093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2034279673/5000000000 : ℝ)|^4501 ≤ (15609474868153/50000000000000 : ℝ)^3477
        have hw : |(2034279673/5000000000 : ℝ)|=(2034279673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4384310733/10000000000 : ℝ)|^4501 ≤ (6878105655359/20000000000000 : ℝ)^3477
        have hw : |(4384310733/10000000000 : ℝ)|=(4384310733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137009691/312500000 : ℝ)|^4501 ≤ (34390521971093/100000000000000 : ℝ)^3477
        have hw : |(137009691/312500000 : ℝ)|=(137009691/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_8 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-31431591/156250000 : ℝ)*x 0 + (2565434631/5000000000 : ℝ)*x 1 + (5424395727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31431591/156250000 : ℝ)^4501 ≤ (250879990109/2000000000000 : ℝ)^3477 := by
    have hnat : (31431591 : ℕ)^4501*2000000000000^3477 ≤ 250879990109^3477*156250000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31431591 156250000 250879990109 2000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2565434631/5000000000 : ℝ)^4501 ≤ (1686165564229/4000000000000 : ℝ)^3477 := by
    have hnat : (2565434631 : ℕ)^4501*4000000000000^3477 ≤ 1686165564229^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565434631 5000000000 1686165564229 4000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424395727/10000000000 : ℝ)^4501 ≤ (45301861375527/100000000000000 : ℝ)^3477 := by
    have hnat : (5424395727 : ℕ)^4501*100000000000000^3477 ≤ 45301861375527^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424395727 10000000000 45301861375527 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31431591/156250000 : ℝ), (2565434631/5000000000 : ℝ), (5424395727/10000000000 : ℝ)] ![(250879990109/2000000000000 : ℝ), (1686165564229/4000000000000 : ℝ), (45301861375527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31431591/156250000 : ℝ)|^4501 ≤ (250879990109/2000000000000 : ℝ)^3477
        have hw : |(-31431591/156250000 : ℝ)|=(31431591/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2565434631/5000000000 : ℝ)|^4501 ≤ (1686165564229/4000000000000 : ℝ)^3477
        have hw : |(2565434631/5000000000 : ℝ)|=(2565434631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424395727/10000000000 : ℝ)|^4501 ≤ (45301861375527/100000000000000 : ℝ)^3477
        have hw : |(5424395727/10000000000 : ℝ)|=(5424395727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_9 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628179329/5000000000 : ℝ)*x 0 + (-921792717/5000000000 : ℝ)*x 1 + (5424395419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628179329/5000000000 : ℝ)^4501 ≤ (43493547602337/100000000000000 : ℝ)^3477 := by
    have hnat : (2628179329 : ℕ)^4501*100000000000000^3477 ≤ 43493547602337^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628179329 5000000000 43493547602337 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921792717/5000000000 : ℝ)^4501 ≤ (11204594335807/100000000000000 : ℝ)^3477 := by
    have hnat : (921792717 : ℕ)^4501*100000000000000^3477 ≤ 11204594335807^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921792717 5000000000 11204594335807 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424395419/10000000000 : ℝ)^4501 ≤ (9060371609143/20000000000000 : ℝ)^3477 := by
    have hnat : (5424395419 : ℕ)^4501*20000000000000^3477 ≤ 9060371609143^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424395419 10000000000 9060371609143 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628179329/5000000000 : ℝ), (-921792717/5000000000 : ℝ), (5424395419/10000000000 : ℝ)] ![(43493547602337/100000000000000 : ℝ), (11204594335807/100000000000000 : ℝ), (9060371609143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628179329/5000000000 : ℝ)|^4501 ≤ (43493547602337/100000000000000 : ℝ)^3477
        have hw : |(2628179329/5000000000 : ℝ)|=(2628179329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-921792717/5000000000 : ℝ)|^4501 ≤ (11204594335807/100000000000000 : ℝ)^3477
        have hw : |(-921792717/5000000000 : ℝ)|=(921792717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424395419/10000000000 : ℝ)|^4501 ≤ (9060371609143/20000000000000 : ℝ)^3477
        have hw : |(5424395419/10000000000 : ℝ)|=(5424395419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_10 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256358099/10000000000 : ℝ)*x 0 + (1356099249/2500000000 : ℝ)*x 1 + (-460896007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256358099/10000000000 : ℝ)^4501 ≤ (43493541614693/100000000000000 : ℝ)^3477 := by
    have hnat : (5256358099 : ℕ)^4501*100000000000000^3477 ≤ 43493541614693^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256358099 10000000000 43493541614693 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356099249/2500000000 : ℝ)^4501 ≤ (9060375018957/20000000000000 : ℝ)^3477 := by
    have hnat : (1356099249 : ℕ)^4501*20000000000000^3477 ≤ 9060375018957^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356099249 2500000000 9060375018957 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460896007/2500000000 : ℝ)^4501 ≤ (2801145818523/25000000000000 : ℝ)^3477 := by
    have hnat : (460896007 : ℕ)^4501*25000000000000^3477 ≤ 2801145818523^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460896007 2500000000 2801145818523 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256358099/10000000000 : ℝ), (1356099249/2500000000 : ℝ), (-460896007/2500000000 : ℝ)] ![(43493541614693/100000000000000 : ℝ), (9060375018957/20000000000000 : ℝ), (2801145818523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256358099/10000000000 : ℝ)|^4501 ≤ (43493541614693/100000000000000 : ℝ)^3477
        have hw : |(5256358099/10000000000 : ℝ)|=(5256358099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356099249/2500000000 : ℝ)|^4501 ≤ (9060375018957/20000000000000 : ℝ)^3477
        have hw : |(1356099249/2500000000 : ℝ)|=(1356099249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-460896007/2500000000 : ℝ)|^4501 ≤ (2801145818523/25000000000000 : ℝ)^3477
        have hw : |(-460896007/2500000000 : ℝ)|=(460896007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_11 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4529029633/10000000000 : ℝ)*x 0 + (4153620159/10000000000 : ℝ)*x 1 + (519202417/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4529029633/10000000000 : ℝ)^4501 ≤ (35867107757309/100000000000000 : ℝ)^3477 := by
    have hnat : (4529029633 : ℕ)^4501*100000000000000^3477 ≤ 35867107757309^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529029633 10000000000 35867107757309 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153620159/10000000000 : ℝ)^4501 ≤ (16033225112261/50000000000000 : ℝ)^3477 := by
    have hnat : (4153620159 : ℕ)^4501*50000000000000^3477 ≤ 16033225112261^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153620159 10000000000 16033225112261 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519202417/1250000000 : ℝ)^4501 ≤ (32066441999667/100000000000000 : ℝ)^3477 := by
    have hnat : (519202417 : ℕ)^4501*100000000000000^3477 ≤ 32066441999667^3477*1250000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519202417 1250000000 32066441999667 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4529029633/10000000000 : ℝ), (4153620159/10000000000 : ℝ), (519202417/1250000000 : ℝ)] ![(35867107757309/100000000000000 : ℝ), (16033225112261/50000000000000 : ℝ), (32066441999667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4529029633/10000000000 : ℝ)|^4501 ≤ (35867107757309/100000000000000 : ℝ)^3477
        have hw : |(4529029633/10000000000 : ℝ)|=(4529029633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4153620159/10000000000 : ℝ)|^4501 ≤ (16033225112261/50000000000000 : ℝ)^3477
        have hw : |(4153620159/10000000000 : ℝ)|=(4153620159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519202417/1250000000 : ℝ)|^4501 ≤ (32066441999667/100000000000000 : ℝ)^3477
        have hw : |(519202417/1250000000 : ℝ)|=(519202417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_12 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-87980773/500000000 : ℝ)*x 0 + (1378171117/2500000000 : ℝ)*x 1 + (5228270633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87980773/500000000 : ℝ)^4501 ≤ (329638723503/3125000000000 : ℝ)^3477 := by
    have hnat : (87980773 : ℕ)^4501*3125000000000^3477 ≤ 329638723503^3477*500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87980773 500000000 329638723503 3125000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378171117/2500000000 : ℝ)^4501 ≤ (11564659205707/25000000000000 : ℝ)^3477 := by
    have hnat : (1378171117 : ℕ)^4501*25000000000000^3477 ≤ 11564659205707^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378171117 2500000000 11564659205707 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228270633/10000000000 : ℝ)^4501 ≤ (10798231000817/25000000000000 : ℝ)^3477 := by
    have hnat : (5228270633 : ℕ)^4501*25000000000000^3477 ≤ 10798231000817^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228270633 10000000000 10798231000817 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87980773/500000000 : ℝ), (1378171117/2500000000 : ℝ), (5228270633/10000000000 : ℝ)] ![(329638723503/3125000000000 : ℝ), (11564659205707/25000000000000 : ℝ), (10798231000817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87980773/500000000 : ℝ)|^4501 ≤ (329638723503/3125000000000 : ℝ)^3477
        have hw : |(-87980773/500000000 : ℝ)|=(87980773/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1378171117/2500000000 : ℝ)|^4501 ≤ (11564659205707/25000000000000 : ℝ)^3477
        have hw : |(1378171117/2500000000 : ℝ)|=(1378171117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228270633/10000000000 : ℝ)|^4501 ≤ (10798231000817/25000000000000 : ℝ)^3477
        have hw : |(5228270633/10000000000 : ℝ)|=(5228270633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_13 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393017151/10000000000 : ℝ)*x 0 + (-1924361771/10000000000 : ℝ)*x 1 + (2614135313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393017151/10000000000 : ℝ)^4501 ≤ (44962914502223/100000000000000 : ℝ)^3477 := by
    have hnat : (5393017151 : ℕ)^4501*100000000000000^3477 ≤ 44962914502223^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393017151 10000000000 44962914502223 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1924361771/10000000000 : ℝ)^4501 ≤ (11844161557851/100000000000000 : ℝ)^3477 := by
    have hnat : (1924361771 : ℕ)^4501*100000000000000^3477 ≤ 11844161557851^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924361771 10000000000 11844161557851 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614135313/5000000000 : ℝ)^4501 ≤ (43192923928407/100000000000000 : ℝ)^3477 := by
    have hnat : (2614135313 : ℕ)^4501*100000000000000^3477 ≤ 43192923928407^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614135313 5000000000 43192923928407 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393017151/10000000000 : ℝ), (-1924361771/10000000000 : ℝ), (2614135313/5000000000 : ℝ)] ![(44962914502223/100000000000000 : ℝ), (11844161557851/100000000000000 : ℝ), (43192923928407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393017151/10000000000 : ℝ)|^4501 ≤ (44962914502223/100000000000000 : ℝ)^3477
        have hw : |(5393017151/10000000000 : ℝ)|=(5393017151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1924361771/10000000000 : ℝ)|^4501 ≤ (11844161557851/100000000000000 : ℝ)^3477
        have hw : |(-1924361771/10000000000 : ℝ)|=(1924361771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614135313/5000000000 : ℝ)|^4501 ≤ (43192923928407/100000000000000 : ℝ)^3477
        have hw : |(2614135313/5000000000 : ℝ)|=(2614135313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_14 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696508613/5000000000 : ℝ)*x 0 + (5228270457/10000000000 : ℝ)*x 1 + (-384872379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696508613/5000000000 : ℝ)^4501 ≤ (44962915311669/100000000000000 : ℝ)^3477 := by
    have hnat : (2696508613 : ℕ)^4501*100000000000000^3477 ≤ 44962915311669^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696508613 5000000000 44962915311669 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228270457/10000000000 : ℝ)^4501 ≤ (43192922121043/100000000000000 : ℝ)^3477 := by
    have hnat : (5228270457 : ℕ)^4501*100000000000000^3477 ≤ 43192922121043^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228270457 10000000000 43192922121043 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384872379/2000000000 : ℝ)^4501 ≤ (11844162545821/100000000000000 : ℝ)^3477 := by
    have hnat : (384872379 : ℕ)^4501*100000000000000^3477 ≤ 11844162545821^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384872379 2000000000 11844162545821 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696508613/5000000000 : ℝ), (5228270457/10000000000 : ℝ), (-384872379/2000000000 : ℝ)] ![(44962915311669/100000000000000 : ℝ), (43192922121043/100000000000000 : ℝ), (11844162545821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696508613/5000000000 : ℝ)|^4501 ≤ (44962915311669/100000000000000 : ℝ)^3477
        have hw : |(2696508613/5000000000 : ℝ)|=(2696508613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228270457/10000000000 : ℝ)|^4501 ≤ (43192922121043/100000000000000 : ℝ)^3477
        have hw : |(5228270457/10000000000 : ℝ)|=(5228270457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-384872379/2000000000 : ℝ)|^4501 ≤ (11844162545821/100000000000000 : ℝ)^3477
        have hw : |(-384872379/2000000000 : ℝ)|=(384872379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_box_15 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4029421307/10000000000 : ℝ)*x 0 + (880682767/2000000000 : ℝ)*x 1 + (2201707047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4029421307/10000000000 : ℝ)^4501 ≤ (30830742171961/100000000000000 : ℝ)^3477 := by
    have hnat : (4029421307 : ℕ)^4501*100000000000000^3477 ≤ 30830742171961^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029421307 10000000000 30830742171961 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880682767/2000000000 : ℝ)^4501 ≤ (6916925518893/20000000000000 : ℝ)^3477 := by
    have hnat : (880682767 : ℕ)^4501*20000000000000^3477 ≤ 6916925518893^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880682767 2000000000 6916925518893 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201707047/5000000000 : ℝ)^4501 ≤ (34584630227749/100000000000000 : ℝ)^3477 := by
    have hnat : (2201707047 : ℕ)^4501*100000000000000^3477 ≤ 34584630227749^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201707047 5000000000 34584630227749 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4029421307/10000000000 : ℝ), (880682767/2000000000 : ℝ), (2201707047/5000000000 : ℝ)] ![(30830742171961/100000000000000 : ℝ), (6916925518893/20000000000000 : ℝ), (34584630227749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4029421307/10000000000 : ℝ)|^4501 ≤ (30830742171961/100000000000000 : ℝ)^3477
        have hw : |(4029421307/10000000000 : ℝ)|=(4029421307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(880682767/2000000000 : ℝ)|^4501 ≤ (6916925518893/20000000000000 : ℝ)^3477
        have hw : |(880682767/2000000000 : ℝ)|=(880682767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2201707047/5000000000 : ℝ)|^4501 ≤ (34584630227749/100000000000000 : ℝ)^3477
        have hw : |(2201707047/5000000000 : ℝ)|=(2201707047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1502_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10877/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63727/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58581/100000 : ℝ) ∧ (80211/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85937/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10877/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10877/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10877/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10877/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10877/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10877/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10877/100000 : ℝ) ^ (4499/1024 : ℝ) ≤ (730735452734963/12500000000000000000 : ℝ) := by
    have hpowers : (10877/100000 : ℝ)^4499 ≤ (730735452734963/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10877 : ℕ)^4499*12500000000000000000^1024 ≤ 730735452734963^1024*100000^4499 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10877 100000 730735452734963 12500000000000000000 4499 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10877/100000 : ℝ)) (X := (730735452734963/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4499/1024 : ℝ) ≤ (27555886502654989/100000000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4499 ≤ (27555886502654989/100000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4499*100000000000000000000^1024 ≤ 27555886502654989^1024*2500^4499 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 27555886502654989 100000000000000000000 4499 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (27555886502654989/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250730735452734963/6250000000000000000 : ℝ) ≤ (10000266099780031/10000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (6250730735452734963/6250000000000000000 : ℝ)^1024 ≤ (10000266099780031/10000000000000000 : ℝ)^4499 := by
      have hnat : (6250730735452734963 : ℕ)^1024*10000000000000000^4499 ≤ 10000266099780031^4499*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250730735452734963 6250000000000000000 10000266099780031 10000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000266099780031/10000000000000000 : ℝ)) (X := (6250730735452734963/6250000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033401770124534693/100000000000000000000 : ℝ) ≤ (2000152029345871/2000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (100033401770124534693/100000000000000000000 : ℝ)^1024 ≤ (2000152029345871/2000000000000000 : ℝ)^4499 := by
      have hnat : (100033401770124534693 : ℕ)^1024*2000000000000000^4499 ≤ 2000152029345871^4499*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033401770124534693 100000000000000000000 2000152029345871 2000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000152029345871/2000000000000000 : ℝ)) (X := (100033401770124534693/100000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027555886502654989/50000000000000000000 : ℝ) ≤ (10001254193678679/10000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (50027555886502654989/50000000000000000000 : ℝ)^1024 ≤ (10001254193678679/10000000000000000 : ℝ)^4499 := by
      have hnat : (50027555886502654989 : ℕ)^1024*10000000000000000^4499 ≤ 10001254193678679^4499*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027555886502654989 50000000000000000000 10001254193678679 10000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001254193678679/10000000000000000 : ℝ)) (X := (50027555886502654989/50000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(730735452734963/12500000000000000000 : ℝ) ≤ ((46020477359951888397/46030000000000000000 : ℝ)+2*(123511737331/115075000000000 : ℝ)*(10877/100000 : ℝ))^(4499/1024 : ℝ) := by
    rw [show (46020477359951888397/46030000000000000000 : ℝ)+2*(123511737331/115075000000000 : ℝ)*(10877/100000 : ℝ)=(10000266099780031/10000000000000000 : ℝ) by norm_num, show 1+2*(730735452734963/12500000000000000000 : ℝ)=(6250730735452734963/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27555886502654989/100000000000000000000 : ℝ)+(730735452734963/12500000000000000000 : ℝ) ≤ ((46020477359951888397/46030000000000000000 : ℝ)+(123511737331/115075000000000 : ℝ)*((387/2500 : ℝ)+(10877/100000 : ℝ)))^(4499/1024 : ℝ) := by
    rw [show (46020477359951888397/46030000000000000000 : ℝ)+(123511737331/115075000000000 : ℝ)*((387/2500 : ℝ)+(10877/100000 : ℝ))=(2000152029345871/2000000000000000 : ℝ) by norm_num, show 1+(27555886502654989/100000000000000000000 : ℝ)+(730735452734963/12500000000000000000 : ℝ)=(100033401770124534693/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27555886502654989/100000000000000000000 : ℝ) ≤ ((46020477359951888397/46030000000000000000 : ℝ)+2*(123511737331/115075000000000 : ℝ)*(387/2500 : ℝ))^(4499/1024 : ℝ) := by
    rw [show (46020477359951888397/46030000000000000000 : ℝ)+2*(123511737331/115075000000000 : ℝ)*(387/2500 : ℝ)=(10001254193678679/10000000000000000 : ℝ) by norm_num, show 1+2*(27555886502654989/100000000000000000000 : ℝ)=(50027555886502654989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46020477359951888397/46030000000000000000 : ℝ)*(X 1 0+X 2 0)+(123511737331/115075000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (10877/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (46020477359951888397/46030000000000000000 : ℝ)) (alpha := (123511737331/115075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46020477359951888397/46030000000000000000 : ℝ)*(X 0 1+X 2 1)+(123511737331/115075000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (10877/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (46020477359951888397/46030000000000000000 : ℝ)) (alpha := (123511737331/115075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46020477359951888397/46030000000000000000 : ℝ)*(X 0 2+X 1 2)+(123511737331/115075000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (10877/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (46020477359951888397/46030000000000000000 : ℝ)) (alpha := (123511737331/115075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1667463033/10000000000 : ℝ)*X 0 0+(675489263/1250000000 : ℝ)*X 0 1+(675489129/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270636333/10000000000 : ℝ)*X 1 0+(-1852263283/10000000000 : ℝ)*X 1 1+(1350978231/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270637641/10000000000 : ℝ)*X 2 0+(5403912527/10000000000 : ℝ)*X 2 1+(-37045241/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2238988033/5000000000 : ℝ)*X 0 0+(4179736613/10000000000 : ℝ)*X 0 1+(261233669/625000000 : ℝ)*X 0 2+(2238988033/5000000000 : ℝ)*X 1 0+(4179736613/10000000000 : ℝ)*X 1 1+(261233669/625000000 : ℝ)*X 1 2+(2238988033/5000000000 : ℝ)*X 2 0+(4179736613/10000000000 : ℝ)*X 2 1+(261233669/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-262971243/1250000000 : ℝ)*X 0 0+(5243288243/10000000000 : ℝ)*X 0 1+(1048657651/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1076510723/2000000000 : ℝ)*X 1 0+(-1918362299/10000000000 : ℝ)*X 1 1+(5243288461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2691276957/5000000000 : ℝ)*X 2 0+(5243287989/10000000000 : ℝ)*X 2 1+(-1918362529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2034279673/5000000000 : ℝ)*X 0 0+(4384310733/10000000000 : ℝ)*X 0 1+(137009691/312500000 : ℝ)*X 0 2+(2034279673/5000000000 : ℝ)*X 1 0+(4384310733/10000000000 : ℝ)*X 1 1+(137009691/312500000 : ℝ)*X 1 2+(2034279673/5000000000 : ℝ)*X 2 0+(4384310733/10000000000 : ℝ)*X 2 1+(137009691/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-31431591/156250000 : ℝ)*X 0 0+(2565434631/5000000000 : ℝ)*X 0 1+(5424395727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628179329/5000000000 : ℝ)*X 1 0+(-921792717/5000000000 : ℝ)*X 1 1+(5424395419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256358099/10000000000 : ℝ)*X 2 0+(1356099249/2500000000 : ℝ)*X 2 1+(-460896007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4529029633/10000000000 : ℝ)*X 0 0+(4153620159/10000000000 : ℝ)*X 0 1+(519202417/1250000000 : ℝ)*X 0 2+(4529029633/10000000000 : ℝ)*X 1 0+(4153620159/10000000000 : ℝ)*X 1 1+(519202417/1250000000 : ℝ)*X 1 2+(4529029633/10000000000 : ℝ)*X 2 0+(4153620159/10000000000 : ℝ)*X 2 1+(519202417/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-87980773/500000000 : ℝ)*X 0 0+(1378171117/2500000000 : ℝ)*X 0 1+(5228270633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5393017151/10000000000 : ℝ)*X 1 0+(-1924361771/10000000000 : ℝ)*X 1 1+(2614135313/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2696508613/5000000000 : ℝ)*X 2 0+(5228270457/10000000000 : ℝ)*X 2 1+(-384872379/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4029421307/10000000000 : ℝ)*X 0 0+(880682767/2000000000 : ℝ)*X 0 1+(2201707047/5000000000 : ℝ)*X 0 2+(4029421307/10000000000 : ℝ)*X 1 0+(880682767/2000000000 : ℝ)*X 1 1+(2201707047/5000000000 : ℝ)*X 1 2+(4029421307/10000000000 : ℝ)*X 2 0+(880682767/2000000000 : ℝ)*X 2 1+(2201707047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63727/100000 : ℝ) ≤ (-14666106631002916168696809147/23015000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2631759/100000000000000 : ℝ)*(upper0) + (3417883/5000000000000 : ℝ)*(upper1) + (107032899/100000000000000 : ℝ)*(upper3) + (17987491/25000000000000 : ℝ)*(upper5) + (2208631244847173/100000000000000 : ℝ)*(major0) + (2208631244847173/100000000000000 : ℝ)*(major1) + (2208631244847173/100000000000000 : ℝ)*(major2) + (8228709023/100000000000000 : ℝ)*(sp2) + (2309649673/50000000000000 : ℝ)*(sp3) + (770005046375257/25000000000000 : ℝ)*(sp4) + (308002155337453/10000000000000 : ℝ)*(sp5) + (770003331166377/25000000000000 : ℝ)*(sp6) + (1358477690951957/100000000000000 : ℝ)*(sp7) + (683936751/50000000000000 : ℝ)*(sp8) + (1358482310251303/100000000000000 : ℝ)*(f.failure) + (308002155337453/10000000000000 : ℝ)*(f.sum) + (7474761138059/11507500000000000000000000000 : ℝ)*base66 + (48203856834201151681/4603000000000000000000000000000000 : ℝ)*base67 + (237591855988663848319/4603000000000000000000000000000000 : ℝ)*base70 + (18428430729598151681/4603000000000000000000000000000000 : ℝ)*base71 + (725843322583/23015000000000000000000000000 : ℝ)*base74 + (47646174887028151681/4603000000000000000000000000000000 : ℝ)*base75 + (1759899674716848319/4603000000000000000000000000000000 : ℝ)*base78 + (2768408224413848319/4603000000000000000000000000000000 : ℝ)*base80 + (249513930482619/11507500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4941691/2500000000000000000000 : ℝ)*base89 + (4941691/2500000000000000000000 : ℝ)*base91 + (4941691/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58581/100000 : ℝ) ≤ (134829120162484497695305017594123/230150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21180981/20000000000000 : ℝ)*(upper0) + (470377507/100000000000000 : ℝ)*(lower1) + (2336703/400000000000 : ℝ)*(upper4) + (228418725729053/10000000000000 : ℝ)*(major0) + (228418725729053/10000000000000 : ℝ)*(major1) + (228418725729053/10000000000000 : ℝ)*(major2) + (1571943514968939/50000000000000 : ℝ)*(sp0) + (1571820402128583/50000000000000 : ℝ)*(sp1) + (24560640294441/781250000000 : ℝ)*(sp2) + (351236334222631/25000000000000 : ℝ)*(sp3) + (9876692603/100000000000000 : ℝ)*(sp7) + (4554330017/100000000000000 : ℝ)*(sp8) + (25078001073/10000000000000 : ℝ)*(sp9) + (16203322431/12500000000000 : ℝ)*(sp10) + (1404955213583127/100000000000000 : ℝ)*(f.failure) + (392986448033487/12500000000000 : ℝ)*(f.sum) + (1164712910461/287687500000000000000000000 : ℝ)*base66 + (20786350079401959/460300000000000000000000000000000 : ℝ)*base68 + (323530059147598041/460300000000000000000000000000000 : ℝ)*base69 + (7118150606118301959/460300000000000000000000000000000 : ℝ)*base72 + (14081871211861/920600000000000000000000000 : ℝ)*base73 + (3134517787132101959/460300000000000000000000000000000 : ℝ)*base76 + (5450855583408901959/460300000000000000000000000000000 : ℝ)*base78 + (2188811285179198041/460300000000000000000000000000000 : ℝ)*base79 + (343031527827/115075000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (22791019/2500000000000000000000 : ℝ)*base89 + (22791019/2500000000000000000000 : ℝ)*base91 + (22791019/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80211/100000 : ℝ) ≤ (46152912768058226724003312507189/57537500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7690909/50000000000000 : ℝ)*(lower2) + (108188017/100000000000000 : ℝ)*(lower3) + (292752093/100000000000000 : ℝ)*(upper4) + (11531599/20000000000000 : ℝ)*(lower5) + (61981749368179/2500000000000 : ℝ)*(major0) + (61981749368179/2500000000000 : ℝ)*(major1) + (61981749368179/2500000000000 : ℝ)*(major2) + (1590071771/100000000000000 : ℝ)*(sp1) + (87686179381/25000000000000 : ℝ)*(sp2) + (9064141933/10000000000000 : ℝ)*(sp3) + (212928475831719/6250000000000 : ℝ)*(sp8) + (851713505808933/25000000000000 : ℝ)*(sp9) + (170325243429499/5000000000000 : ℝ)*(sp10) + (762427910360897/50000000000000 : ℝ)*(sp11) + (1524946462141123/100000000000000 : ℝ)*(f.failure) + (212928475831719/6250000000000 : ℝ)*(f.sum) + (3391082303789/460300000000000000000000000 : ℝ)*base66 + (1822095174633080937/115075000000000000000000000000000 : ℝ)*base68 + (361006927952319063/115075000000000000000000000000000 : ℝ)*base69 + (502769988602855937/115075000000000000000000000000000 : ℝ)*base72 + (38233282012997/4603000000000000000000000000 : ℝ)*base74 + (524672956139519063/115075000000000000000000000000000 : ℝ)*base75 + (1032868212590730937/115075000000000000000000000000000 : ℝ)*base78 + (540180523921580937/115075000000000000000000000000000 : ℝ)*base80 + (1612455761647/575375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13863769/2500000000000000000000 : ℝ)*base90 + (13863769/2500000000000000000000 : ℝ)*base92 + (13863769/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-85937/100000 : ℝ) ≤ (-123611819232662317075813367621541/143843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21947051/100000000000000 : ℝ)*(lower0) + (24343753/50000000000000 : ℝ)*(lower1) + (329309/1250000000000 : ℝ)*(lower4) + (2518092738247461/100000000000000 : ℝ)*(major0) + (2518092738247461/100000000000000 : ℝ)*(major1) + (1259046369123731/50000000000000 : ℝ)*(major2) + (2609061/25000000000000 : ℝ)*(sp0) + (8545175509/25000000000000 : ℝ)*(sp5) + (16912399603/20000000000000 : ℝ)*(sp6) + (10069381789/100000000000000 : ℝ)*(sp7) + (1758002436470937/50000000000000 : ℝ)*(sp12) + (1757985351338041/50000000000000 : ℝ)*(sp13) + (3515920321380103/100000000000000 : ℝ)*(sp14) + (193601931564571/12500000000000 : ℝ)*(sp15) + (1548825521898357/100000000000000 : ℝ)*(f.failure) + (1758002441689059/50000000000000 : ℝ)*(f.sum) + (8761257860357/2876875000000000000000000000 : ℝ)*base65 + (30952964212265589983/4603000000000000000000000000000000 : ℝ)*base68 + (1134504708800550793/2301500000000000000000000000000000 : ℝ)*base70 + (16377789647066589983/4603000000000000000000000000000000 : ℝ)*base72 + (52349333263561/23015000000000000000000000000 : ℝ)*base73 + (6300119912017550793/2301500000000000000000000000000000 : ℝ)*base76 + (34553773662996989983/4603000000000000000000000000000000 : ℝ)*base78 + (19323915779491989983/4603000000000000000000000000000000 : ℝ)*base80 + (13181298155809/5753750000000000000000000000 : ℝ)*base82 + (9241329/2500000000000000000000 : ℝ)*base89 + (9241329/2500000000000000000000 : ℝ)*base91 + (15758671/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1502_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10877/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63727/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58581/100000 : ℝ) else (80211/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85937/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1502_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1502_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63727/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58581/100000 : ℝ) else (80211/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85937/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1502_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1502_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63727/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58581/100000 : ℝ) else (80211/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85937/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1502_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

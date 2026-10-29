-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1344_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:05:23.525544+00:00
-- url     : https://prove2.me/submissions/f5cbe25f-6355-42ca-b58a-322b3f9664c1

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
theorem support_rectangle_w1344_s0_0 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-451991123/2500000000 : ℝ)*x 0 + (29980267/50000000 : ℝ)*x 1 + (2405692991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451991123/2500000000 : ℝ)^269 ≤ (2649892248119/25000000000000 : ℝ)^205 := by
    have hnat : (451991123 : ℕ)^269*25000000000000^205 ≤ 2649892248119^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451991123 2500000000 2649892248119 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29980267/50000000 : ℝ)^269 ≤ (25555606154753/50000000000000 : ℝ)^205 := by
    have hnat : (29980267 : ℕ)^269*50000000000000^205 ≤ 25555606154753^205*50000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29980267 50000000 25555606154753 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2405692991/5000000000 : ℝ)^269 ≤ (38289218688167/100000000000000 : ℝ)^205 := by
    have hnat : (2405692991 : ℕ)^269*100000000000000^205 ≤ 38289218688167^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405692991 5000000000 38289218688167 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-451991123/2500000000 : ℝ), (29980267/50000000 : ℝ), (2405692991/5000000000 : ℝ)] ![(2649892248119/25000000000000 : ℝ), (25555606154753/50000000000000 : ℝ), (38289218688167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-451991123/2500000000 : ℝ)|^269 ≤ (2649892248119/25000000000000 : ℝ)^205
        have hw : |(-451991123/2500000000 : ℝ)|=(451991123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(29980267/50000000 : ℝ)|^269 ≤ (25555606154753/50000000000000 : ℝ)^205
        have hw : |(29980267/50000000 : ℝ)|=(29980267/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2405692991/5000000000 : ℝ)|^269 ≤ (38289218688167/100000000000000 : ℝ)^205
        have hw : |(2405692991/5000000000 : ℝ)|=(2405692991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s0_1 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5501588631/10000000000 : ℝ)*x 0 + (-496245241/2000000000 : ℝ)*x 1 + (4811386399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501588631/10000000000 : ℝ)^269 ≤ (45653047018677/100000000000000 : ℝ)^205 := by
    have hnat : (5501588631 : ℕ)^269*100000000000000^205 ≤ 45653047018677^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501588631 10000000000 45653047018677 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496245241/2000000000 : ℝ)^269 ≤ (16057729932229/100000000000000 : ℝ)^205 := by
    have hnat : (496245241 : ℕ)^269*100000000000000^205 ≤ 16057729932229^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496245241 2000000000 16057729932229 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4811386399/10000000000 : ℝ)^269 ≤ (9572305760673/25000000000000 : ℝ)^205 := by
    have hnat : (4811386399 : ℕ)^269*25000000000000^205 ≤ 9572305760673^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4811386399 10000000000 9572305760673 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5501588631/10000000000 : ℝ), (-496245241/2000000000 : ℝ), (4811386399/10000000000 : ℝ)] ![(45653047018677/100000000000000 : ℝ), (16057729932229/100000000000000 : ℝ), (9572305760673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5501588631/10000000000 : ℝ)|^269 ≤ (45653047018677/100000000000000 : ℝ)^205
        have hw : |(5501588631/10000000000 : ℝ)|=(5501588631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496245241/2000000000 : ℝ)|^269 ≤ (16057729932229/100000000000000 : ℝ)^205
        have hw : |(-496245241/2000000000 : ℝ)|=(496245241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4811386399/10000000000 : ℝ)|^269 ≤ (9572305760673/25000000000000 : ℝ)^205
        have hw : |(4811386399/10000000000 : ℝ)|=(4811386399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s0_2 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1100317671/2000000000 : ℝ)*x 0 + (962277233/2000000000 : ℝ)*x 1 + (-496245369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100317671/2000000000 : ℝ)^269 ≤ (5706630501671/12500000000000 : ℝ)^205 := by
    have hnat : (1100317671 : ℕ)^269*12500000000000^205 ≤ 5706630501671^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100317671 2000000000 5706630501671 12500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962277233/2000000000 : ℝ)^269 ≤ (19144610299573/50000000000000 : ℝ)^205 := by
    have hnat : (962277233 : ℕ)^269*50000000000000^205 ≤ 19144610299573^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962277233 2000000000 19144610299573 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496245369/2000000000 : ℝ)^269 ≤ (16057735367187/100000000000000 : ℝ)^205 := by
    have hnat : (496245369 : ℕ)^269*100000000000000^205 ≤ 16057735367187^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496245369 2000000000 16057735367187 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100317671/2000000000 : ℝ), (962277233/2000000000 : ℝ), (-496245369/2000000000 : ℝ)] ![(5706630501671/12500000000000 : ℝ), (19144610299573/50000000000000 : ℝ), (16057735367187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100317671/2000000000 : ℝ)|^269 ≤ (5706630501671/12500000000000 : ℝ)^205
        have hw : |(1100317671/2000000000 : ℝ)|=(1100317671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(962277233/2000000000 : ℝ)|^269 ≤ (19144610299573/50000000000000 : ℝ)^205
        have hw : |(962277233/2000000000 : ℝ)|=(962277233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-496245369/2000000000 : ℝ)|^269 ≤ (16057735367187/100000000000000 : ℝ)^205
        have hw : |(-496245369/2000000000 : ℝ)|=(496245369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s0_3 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1044611857/2500000000 : ℝ)*x 0 + (77661669/250000000 : ℝ)*x 1 + (5589704823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044611857/2500000000 : ℝ)^269 ≤ (7954953855369/25000000000000 : ℝ)^205 := by
    have hnat : (1044611857 : ℕ)^269*25000000000000^205 ≤ 7954953855369^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044611857 2500000000 7954953855369 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77661669/250000000 : ℝ)^269 ≤ (21565267758767/100000000000000 : ℝ)^205 := by
    have hnat : (77661669 : ℕ)^269*100000000000000^205 ≤ 21565267758767^205*250000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77661669 250000000 21565267758767 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5589704823/10000000000 : ℝ)^269 ≤ (23307458403941/50000000000000 : ℝ)^205 := by
    have hnat : (5589704823 : ℕ)^269*50000000000000^205 ≤ 23307458403941^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589704823 10000000000 23307458403941 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044611857/2500000000 : ℝ), (77661669/250000000 : ℝ), (5589704823/10000000000 : ℝ)] ![(7954953855369/25000000000000 : ℝ), (21565267758767/100000000000000 : ℝ), (23307458403941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044611857/2500000000 : ℝ)|^269 ≤ (7954953855369/25000000000000 : ℝ)^205
        have hw : |(1044611857/2500000000 : ℝ)|=(1044611857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77661669/250000000 : ℝ)|^269 ≤ (21565267758767/100000000000000 : ℝ)^205
        have hw : |(77661669/250000000 : ℝ)|=(77661669/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5589704823/10000000000 : ℝ)|^269 ≤ (23307458403941/50000000000000 : ℝ)^205
        have hw : |(5589704823/10000000000 : ℝ)|=(5589704823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s0_4 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1812410607/10000000000 : ℝ)*x 0 + (4841872951/10000000000 : ℝ)*x 1 + (5964477901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1812410607/10000000000 : ℝ)^269 ≤ (10633786156187/100000000000000 : ℝ)^205 := by
    have hnat : (1812410607 : ℕ)^269*100000000000000^205 ≤ 10633786156187^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812410607 10000000000 10633786156187 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4841872951/10000000000 : ℝ)^269 ≤ (19303946736251/50000000000000 : ℝ)^205 := by
    have hnat : (4841872951 : ℕ)^269*50000000000000^205 ≤ 19303946736251^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4841872951 10000000000 19303946736251 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5964477901/10000000000 : ℝ)^269 ≤ (5075832035663/10000000000000 : ℝ)^205 := by
    have hnat : (5964477901 : ℕ)^269*10000000000000^205 ≤ 5075832035663^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5964477901 10000000000 5075832035663 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1812410607/10000000000 : ℝ), (4841872951/10000000000 : ℝ), (5964477901/10000000000 : ℝ)] ![(10633786156187/100000000000000 : ℝ), (19303946736251/50000000000000 : ℝ), (5075832035663/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1812410607/10000000000 : ℝ)|^269 ≤ (10633786156187/100000000000000 : ℝ)^205
        have hw : |(-1812410607/10000000000 : ℝ)|=(1812410607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4841872951/10000000000 : ℝ)|^269 ≤ (19303946736251/50000000000000 : ℝ)^205
        have hw : |(4841872951/10000000000 : ℝ)|=(4841872951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5964477901/10000000000 : ℝ)|^269 ≤ (5075832035663/10000000000000 : ℝ)^205
        have hw : |(5964477901/10000000000 : ℝ)|=(5964477901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s0_5 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5178715347/10000000000 : ℝ)*x 0 + (-1328135701/10000000000 : ℝ)*x 1 + (1491119413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178715347/10000000000 : ℝ)^269 ≤ (4216999555873/10000000000000 : ℝ)^205 := by
    have hnat : (5178715347 : ℕ)^269*10000000000000^205 ≤ 4216999555873^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178715347 10000000000 4216999555873 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1328135701/10000000000 : ℝ)^269 ≤ (707168685101/10000000000000 : ℝ)^205 := by
    have hnat : (1328135701 : ℕ)^269*10000000000000^205 ≤ 707168685101^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328135701 10000000000 707168685101 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1491119413/2500000000 : ℝ)^269 ≤ (12689579394017/25000000000000 : ℝ)^205 := by
    have hnat : (1491119413 : ℕ)^269*25000000000000^205 ≤ 12689579394017^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491119413 2500000000 12689579394017 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178715347/10000000000 : ℝ), (-1328135701/10000000000 : ℝ), (1491119413/2500000000 : ℝ)] ![(4216999555873/10000000000000 : ℝ), (707168685101/10000000000000 : ℝ), (12689579394017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178715347/10000000000 : ℝ)|^269 ≤ (4216999555873/10000000000000 : ℝ)^205
        have hw : |(5178715347/10000000000 : ℝ)|=(5178715347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1328135701/10000000000 : ℝ)|^269 ≤ (707168685101/10000000000000 : ℝ)^205
        have hw : |(-1328135701/10000000000 : ℝ)|=(1328135701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1491119413/2500000000 : ℝ)|^269 ≤ (12689579394017/25000000000000 : ℝ)^205
        have hw : |(1491119413/2500000000 : ℝ)|=(1491119413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s0_6 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (80917427/156250000 : ℝ)*x 0 + (5964477909/10000000000 : ℝ)*x 1 + (-664067659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80917427/156250000 : ℝ)^269 ≤ (42169995355713/100000000000000 : ℝ)^205 := by
    have hnat : (80917427 : ℕ)^269*100000000000000^205 ≤ 42169995355713^205*156250000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80917427 156250000 42169995355713 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5964477909/10000000000 : ℝ)^269 ≤ (10151664089193/20000000000000 : ℝ)^205 := by
    have hnat : (5964477909 : ℕ)^269*20000000000000^205 ≤ 10151664089193^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5964477909 10000000000 10151664089193 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (664067659/5000000000 : ℝ)^269 ≤ (3535842087531/50000000000000 : ℝ)^205 := by
    have hnat : (664067659 : ℕ)^269*50000000000000^205 ≤ 3535842087531^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664067659 5000000000 3535842087531 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80917427/156250000 : ℝ), (5964477909/10000000000 : ℝ), (-664067659/5000000000 : ℝ)] ![(42169995355713/100000000000000 : ℝ), (10151664089193/20000000000000 : ℝ), (3535842087531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80917427/156250000 : ℝ)|^269 ≤ (42169995355713/100000000000000 : ℝ)^205
        have hw : |(80917427/156250000 : ℝ)|=(80917427/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5964477909/10000000000 : ℝ)|^269 ≤ (10151664089193/20000000000000 : ℝ)^205
        have hw : |(5964477909/10000000000 : ℝ)|=(5964477909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-664067659/5000000000 : ℝ)|^269 ≤ (3535842087531/50000000000000 : ℝ)^205
        have hw : |(-664067659/5000000000 : ℝ)|=(664067659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s0_7 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4187765141/10000000000 : ℝ)*x 0 + (5525800541/10000000000 : ℝ)*x 1 + (3172653121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187765141/10000000000 : ℝ)^269 ≤ (31912956557739/100000000000000 : ℝ)^205 := by
    have hnat : (4187765141 : ℕ)^269*100000000000000^205 ≤ 31912956557739^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187765141 10000000000 31912956557739 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5525800541/10000000000 : ℝ)^269 ≤ (1147921665641/2500000000000 : ℝ)^205 := by
    have hnat : (5525800541 : ℕ)^269*2500000000000^205 ≤ 1147921665641^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525800541 10000000000 1147921665641 2500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3172653121/10000000000 : ℝ)^269 ≤ (22170176809977/100000000000000 : ℝ)^205 := by
    have hnat : (3172653121 : ℕ)^269*100000000000000^205 ≤ 22170176809977^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3172653121 10000000000 22170176809977 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187765141/10000000000 : ℝ), (5525800541/10000000000 : ℝ), (3172653121/10000000000 : ℝ)] ![(31912956557739/100000000000000 : ℝ), (1147921665641/2500000000000 : ℝ), (22170176809977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187765141/10000000000 : ℝ)|^269 ≤ (31912956557739/100000000000000 : ℝ)^205
        have hw : |(4187765141/10000000000 : ℝ)|=(4187765141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5525800541/10000000000 : ℝ)|^269 ≤ (1147921665641/2500000000000 : ℝ)^205
        have hw : |(5525800541/10000000000 : ℝ)|=(5525800541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3172653121/10000000000 : ℝ)|^269 ≤ (22170176809977/100000000000000 : ℝ)^205
        have hw : |(3172653121/10000000000 : ℝ)|=(3172653121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1344_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1429/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26857/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4303/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4303 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4303*1^1024 ≤ 0^1024*1^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4303/1024 : ℝ) ≤ (1063572301877492703/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4303 ≤ (1063572301877492703/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4303*50000000000000000000^1024 ≤ 1063572301877492703^1024*5^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1063572301877492703 50000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1063572301877492703/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4303 := by
      have hnat : (1 : ℕ)^1024*1^4303 ≤ 1^4303*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51063572301877492703/50000000000000000000 : ℝ) ≤ (80401721554589/80000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (51063572301877492703/50000000000000000000 : ℝ)^1024 ≤ (80401721554589/80000000000000 : ℝ)^4303 := by
      have hnat : (51063572301877492703 : ℕ)^1024*80000000000000^4303 ≤ 80401721554589^4303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51063572301877492703 50000000000000000000 80401721554589 80000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80401721554589/80000000000000 : ℝ)) (X := (51063572301877492703/50000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26063572301877492703/25000000000000000000 : ℝ) ≤ (40401721554589/40000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (26063572301877492703/25000000000000000000 : ℝ)^1024 ≤ (40401721554589/40000000000000 : ℝ)^4303 := by
      have hnat : (26063572301877492703 : ℕ)^1024*40000000000000^4303 ≤ 40401721554589^4303*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26063572301877492703 25000000000000000000 40401721554589 40000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40401721554589/40000000000000 : ℝ)) (X := (26063572301877492703/25000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(401721554589/32000000000000 : ℝ)*(0 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(401721554589/32000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1063572301877492703/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(401721554589/32000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4303/1024 : ℝ) := by
    rw [show (1 : ℝ)+(401721554589/32000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(80401721554589/80000000000000 : ℝ) by norm_num, show 1+(1063572301877492703/50000000000000000000 : ℝ)+(0 : ℝ)=(51063572301877492703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1063572301877492703/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(401721554589/32000000000000 : ℝ)*(2/5 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(401721554589/32000000000000 : ℝ)*(2/5 : ℝ)=(40401721554589/40000000000000 : ℝ) by norm_num, show 1+2*(1063572301877492703/50000000000000000000 : ℝ)=(26063572301877492703/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(401721554589/32000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (401721554589/32000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(401721554589/32000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (401721554589/32000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(401721554589/32000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (401721554589/32000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-451991123/2500000000 : ℝ)*X 0 0+(29980267/50000000 : ℝ)*X 0 1+(2405692991/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5501588631/10000000000 : ℝ)*X 1 0+(-496245241/2000000000 : ℝ)*X 1 1+(4811386399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1100317671/2000000000 : ℝ)*X 2 0+(962277233/2000000000 : ℝ)*X 2 1+(-496245369/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1044611857/2500000000 : ℝ)*X 0 0+(77661669/250000000 : ℝ)*X 0 1+(5589704823/10000000000 : ℝ)*X 0 2+(1044611857/2500000000 : ℝ)*X 1 0+(77661669/250000000 : ℝ)*X 1 1+(5589704823/10000000000 : ℝ)*X 1 2+(1044611857/2500000000 : ℝ)*X 2 0+(77661669/250000000 : ℝ)*X 2 1+(5589704823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1812410607/10000000000 : ℝ)*X 0 0+(4841872951/10000000000 : ℝ)*X 0 1+(5964477901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5178715347/10000000000 : ℝ)*X 1 0+(-1328135701/10000000000 : ℝ)*X 1 1+(1491119413/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((80917427/156250000 : ℝ)*X 2 0+(5964477909/10000000000 : ℝ)*X 2 1+(-664067659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4187765141/10000000000 : ℝ)*X 0 0+(5525800541/10000000000 : ℝ)*X 0 1+(3172653121/10000000000 : ℝ)*X 0 2+(4187765141/10000000000 : ℝ)*X 1 0+(5525800541/10000000000 : ℝ)*X 1 1+(3172653121/10000000000 : ℝ)*X 1 2+(4187765141/10000000000 : ℝ)*X 2 0+(5525800541/10000000000 : ℝ)*X 2 1+(3172653121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1264897502978301874479/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59527269/50000000000000 : ℝ)*(base1) + (1500679189/100000000000000 : ℝ)*(base19) + (1458331597/100000000000000 : ℝ)*(base23) + (247489017/100000000000000 : ℝ)*(upper3) + (17598663/25000000000000 : ℝ)*(upper5) + (311708287053263/50000000000000 : ℝ)*(major0) + (311708287053263/50000000000000 : ℝ)*(major1) + (311708287053263/50000000000000 : ℝ)*(major2) + (844124093092477/100000000000000 : ℝ)*(sp0) + (168825377643593/20000000000000 : ℝ)*(sp1) + (844126930565557/100000000000000 : ℝ)*(sp2) + (402701929031253/100000000000000 : ℝ)*(sp3) + (882971843/20000000000000 : ℝ)*(sp4) + (2500413843/100000000000000 : ℝ)*(sp7) + (80540909699927/20000000000000 : ℝ)*(f.failure) + (422064194448577/50000000000000 : ℝ)*(f.sum) + (1592049907507/800000000000000000000000000 : ℝ)*base65 + (25264917701107/1600000000000000000000000000 : ℝ)*base67 + (8420521312307/1600000000000000000000000000 : ℝ)*base69 + (12653932974707/1600000000000000000000000000 : ℝ)*base71 + (5226871859507/800000000000000000000000000 : ℝ)*base73 + (9400852662707/1600000000000000000000000000 : ℝ)*base75 + (16075800462707/1600000000000000000000000000 : ℝ)*base77 + (12843391877107/1600000000000000000000000000 : ℝ)*base79 + (1195082571693/800000000000000000000000000 : ℝ)*base82 + (20842609/2000000000000000000000 : ℝ)*base90 + (20842609/2000000000000000000000 : ℝ)*base92 + (20842609/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6335540821042828653309/800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1737110731/100000000000000 : ℝ)*(base19) + (55332337/3125000000000 : ℝ)*(base23) + (14238383/100000000000000 : ℝ)*(base39) + (229999757/100000000000000 : ℝ)*(upper3) + (100392337/50000000000000 : ℝ)*(upper5) + (328937039496289/50000000000000 : ℝ)*(major0) + (328937039496289/50000000000000 : ℝ)*(major1) + (131574812950839/20000000000000 : ℝ)*(major2) + (1946223303/50000000000000 : ℝ)*(sp1) + (170389501/4000000000000 : ℝ)*(sp2) + (445392514978571/50000000000000 : ℝ)*(sp4) + (178155880079961/20000000000000 : ℝ)*(sp5) + (55673688363951/6250000000000 : ℝ)*(sp6) + (212481424904377/50000000000000 : ℝ)*(sp7) + (212481424904377/50000000000000 : ℝ)*(f.failure) + (445392522097763/50000000000000 : ℝ)*(f.sum) + (3563466907297/3200000000000000000000000000 : ℝ)*base65 + (3364678598331/640000000000000000000000000 : ℝ)*base67 + (3602832138621/1600000000000000000000000000 : ℝ)*base69 + (924687507771/640000000000000000000000000 : ℝ)*base71 + (10175792478497/3200000000000000000000000000 : ℝ)*base73 + (4732990999421/1600000000000000000000000000 : ℝ)*base75 + (10117263561021/1600000000000000000000000000 : ℝ)*base77 + (3103515807421/1600000000000000000000000000 : ℝ)*base79 + (3144959516579/800000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (26165759/5000000000000000000000 : ℝ)*base90 + (26165759/5000000000000000000000 : ℝ)*base92 + (26165759/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1344_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26857/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1344_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1344_s1_0 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-498122293/2500000000 : ℝ)*x 0 + (564124499/1000000000 : ℝ)*x 1 + (2524010509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498122293/2500000000 : ℝ)^269 ≤ (752576801159/6250000000000 : ℝ)^205 := by
    have hnat : (498122293 : ℕ)^269*6250000000000^205 ≤ 752576801159^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498122293 2500000000 752576801159 6250000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564124499/1000000000 : ℝ)^269 ≤ (47179728395387/100000000000000 : ℝ)^205 := by
    have hnat : (564124499 : ℕ)^269*100000000000000^205 ≤ 47179728395387^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564124499 1000000000 47179728395387 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2524010509/5000000000 : ℝ)^269 ≤ (8155808553489/20000000000000 : ℝ)^205 := by
    have hnat : (2524010509 : ℕ)^269*20000000000000^205 ≤ 8155808553489^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524010509 5000000000 8155808553489 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-498122293/2500000000 : ℝ), (564124499/1000000000 : ℝ), (2524010509/5000000000 : ℝ)] ![(752576801159/6250000000000 : ℝ), (47179728395387/100000000000000 : ℝ), (8155808553489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-498122293/2500000000 : ℝ)|^269 ≤ (752576801159/6250000000000 : ℝ)^205
        have hw : |(-498122293/2500000000 : ℝ)|=(498122293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564124499/1000000000 : ℝ)|^269 ≤ (47179728395387/100000000000000 : ℝ)^205
        have hw : |(564124499/1000000000 : ℝ)|=(564124499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2524010509/5000000000 : ℝ)|^269 ≤ (8155808553489/20000000000000 : ℝ)^205
        have hw : |(2524010509/5000000000 : ℝ)|=(2524010509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s1_1 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2702755381/5000000000 : ℝ)*x 0 + (-2308993687/10000000000 : ℝ)*x 1 + (2524010567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702755381/5000000000 : ℝ)^269 ≤ (2788108599867/6250000000000 : ℝ)^205 := by
    have hnat : (2702755381 : ℕ)^269*6250000000000^205 ≤ 2788108599867^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702755381 5000000000 2788108599867 6250000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2308993687/10000000000 : ℝ)^269 ≤ (14611218384501/100000000000000 : ℝ)^205 := by
    have hnat : (2308993687 : ℕ)^269*100000000000000^205 ≤ 14611218384501^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2308993687 10000000000 14611218384501 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2524010567/5000000000 : ℝ)^269 ≤ (40779043997069/100000000000000 : ℝ)^205 := by
    have hnat : (2524010567 : ℕ)^269*100000000000000^205 ≤ 40779043997069^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524010567 5000000000 40779043997069 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2702755381/5000000000 : ℝ), (-2308993687/10000000000 : ℝ), (2524010567/5000000000 : ℝ)] ![(2788108599867/6250000000000 : ℝ), (14611218384501/100000000000000 : ℝ), (40779043997069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2702755381/5000000000 : ℝ)|^269 ≤ (2788108599867/6250000000000 : ℝ)^205
        have hw : |(2702755381/5000000000 : ℝ)|=(2702755381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2308993687/10000000000 : ℝ)|^269 ≤ (14611218384501/100000000000000 : ℝ)^205
        have hw : |(-2308993687/10000000000 : ℝ)|=(2308993687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2524010567/5000000000 : ℝ)|^269 ≤ (40779043997069/100000000000000 : ℝ)^205
        have hw : |(2524010567/5000000000 : ℝ)|=(2524010567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s1_2 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (270275537/500000000 : ℝ)*x 0 + (2524010439/5000000000 : ℝ)*x 1 + (-1154497021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270275537/500000000 : ℝ)^269 ≤ (44609737359633/100000000000000 : ℝ)^205 := by
    have hnat : (270275537 : ℕ)^269*100000000000000^205 ≤ 44609737359633^205*500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270275537 500000000 44609737359633 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2524010439/5000000000 : ℝ)^269 ≤ (5097380160427/12500000000000 : ℝ)^205 := by
    have hnat : (2524010439 : ℕ)^269*12500000000000^205 ≤ 5097380160427^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524010439 5000000000 5097380160427 12500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1154497021/5000000000 : ℝ)^269 ≤ (14611221332249/100000000000000 : ℝ)^205 := by
    have hnat : (1154497021 : ℕ)^269*100000000000000^205 ≤ 14611221332249^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154497021 5000000000 14611221332249 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270275537/500000000 : ℝ), (2524010439/5000000000 : ℝ), (-1154497021/5000000000 : ℝ)] ![(44609737359633/100000000000000 : ℝ), (5097380160427/12500000000000 : ℝ), (14611221332249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270275537/500000000 : ℝ)|^269 ≤ (44609737359633/100000000000000 : ℝ)^205
        have hw : |(270275537/500000000 : ℝ)|=(270275537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2524010439/5000000000 : ℝ)|^269 ≤ (5097380160427/12500000000000 : ℝ)^205
        have hw : |(2524010439/5000000000 : ℝ)|=(2524010439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1154497021/5000000000 : ℝ)|^269 ≤ (14611221332249/100000000000000 : ℝ)^205
        have hw : |(-1154497021/5000000000 : ℝ)|=(1154497021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s1_3 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4291949749/10000000000 : ℝ)*x 0 + (3711905249/10000000000 : ℝ)*x 1 + (4955389943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291949749/10000000000 : ℝ)^269 ≤ (32958785157697/100000000000000 : ℝ)^205 := by
    have hnat : (4291949749 : ℕ)^269*100000000000000^205 ≤ 32958785157697^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291949749 10000000000 32958785157697 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3711905249/10000000000 : ℝ)^269 ≤ (13620628008891/50000000000000 : ℝ)^205 := by
    have hnat : (3711905249 : ℕ)^269*50000000000000^205 ≤ 13620628008891^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3711905249 10000000000 13620628008891 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4955389943/10000000000 : ℝ)^269 ≤ (19899979406089/50000000000000 : ℝ)^205 := by
    have hnat : (4955389943 : ℕ)^269*50000000000000^205 ≤ 19899979406089^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4955389943 10000000000 19899979406089 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291949749/10000000000 : ℝ), (3711905249/10000000000 : ℝ), (4955389943/10000000000 : ℝ)] ![(32958785157697/100000000000000 : ℝ), (13620628008891/50000000000000 : ℝ), (19899979406089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291949749/10000000000 : ℝ)|^269 ≤ (32958785157697/100000000000000 : ℝ)^205
        have hw : |(4291949749/10000000000 : ℝ)|=(4291949749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3711905249/10000000000 : ℝ)|^269 ≤ (13620628008891/50000000000000 : ℝ)^205
        have hw : |(3711905249/10000000000 : ℝ)|=(3711905249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4955389943/10000000000 : ℝ)|^269 ≤ (19899979406089/50000000000000 : ℝ)^205
        have hw : |(4955389943/10000000000 : ℝ)|=(4955389943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s1_4 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-398604431/2000000000 : ℝ)*x 0 + (2527726673/5000000000 : ℝ)*x 1 + (563367767/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398604431/2000000000 : ℝ)^269 ≤ (752840971931/6250000000000 : ℝ)^205 := by
    have hnat : (398604431 : ℕ)^269*6250000000000^205 ≤ 752840971931^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398604431 2000000000 752840971931 6250000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2527726673/5000000000 : ℝ)^269 ≤ (40857845073401/100000000000000 : ℝ)^205 := by
    have hnat : (2527726673 : ℕ)^269*100000000000000^205 ≤ 40857845073401^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527726673 5000000000 40857845073401 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563367767/1000000000 : ℝ)^269 ≤ (9419339871023/20000000000000 : ℝ)^205 := by
    have hnat : (563367767 : ℕ)^269*20000000000000^205 ≤ 9419339871023^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563367767 1000000000 9419339871023 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398604431/2000000000 : ℝ), (2527726673/5000000000 : ℝ), (563367767/1000000000 : ℝ)] ![(752840971931/6250000000000 : ℝ), (40857845073401/100000000000000 : ℝ), (9419339871023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398604431/2000000000 : ℝ)|^269 ≤ (752840971931/6250000000000 : ℝ)^205
        have hw : |(-398604431/2000000000 : ℝ)|=(398604431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2527726673/5000000000 : ℝ)|^269 ≤ (40857845073401/100000000000000 : ℝ)^205
        have hw : |(2527726673/5000000000 : ℝ)|=(2527726673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563367767/1000000000 : ℝ)|^269 ≤ (9419339871023/20000000000000 : ℝ)^205
        have hw : |(563367767/1000000000 : ℝ)|=(563367767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s1_5 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5251551681/10000000000 : ℝ)*x 0 + (-86166839/500000000 : ℝ)*x 1 + (5633677711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251551681/10000000000 : ℝ)^269 ≤ (42949964639023/100000000000000 : ℝ)^205 := by
    have hnat : (5251551681 : ℕ)^269*100000000000000^205 ≤ 42949964639023^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251551681 10000000000 42949964639023 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86166839/500000000 : ℝ)^269 ≤ (9953335540841/100000000000000 : ℝ)^205 := by
    have hnat : (86166839 : ℕ)^269*100000000000000^205 ≤ 9953335540841^205*500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86166839 500000000 9953335540841 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5633677711/10000000000 : ℝ)^269 ≤ (376773598439/800000000000 : ℝ)^205 := by
    have hnat : (5633677711 : ℕ)^269*800000000000^205 ≤ 376773598439^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5633677711 10000000000 376773598439 800000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251551681/10000000000 : ℝ), (-86166839/500000000 : ℝ), (5633677711/10000000000 : ℝ)] ![(42949964639023/100000000000000 : ℝ), (9953335540841/100000000000000 : ℝ), (376773598439/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251551681/10000000000 : ℝ)|^269 ≤ (42949964639023/100000000000000 : ℝ)^205
        have hw : |(5251551681/10000000000 : ℝ)|=(5251551681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86166839/500000000 : ℝ)|^269 ≤ (9953335540841/100000000000000 : ℝ)^205
        have hw : |(-86166839/500000000 : ℝ)|=(86166839/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5633677711/10000000000 : ℝ)|^269 ≤ (376773598439/800000000000 : ℝ)^205
        have hw : |(5633677711/10000000000 : ℝ)|=(5633677711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s1_6 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2625775791/5000000000 : ℝ)*x 0 + (225347111/400000000 : ℝ)*x 1 + (-1723336827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625775791/5000000000 : ℝ)^269 ≤ (10737490894143/25000000000000 : ℝ)^205 := by
    have hnat : (2625775791 : ℕ)^269*25000000000000^205 ≤ 10737490894143^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625775791 5000000000 10737490894143 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225347111/400000000 : ℝ)^269 ≤ (47096700506939/100000000000000 : ℝ)^205 := by
    have hnat : (225347111 : ℕ)^269*100000000000000^205 ≤ 47096700506939^205*400000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225347111 400000000 47096700506939 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1723336827/10000000000 : ℝ)^269 ≤ (4976667948521/50000000000000 : ℝ)^205 := by
    have hnat : (1723336827 : ℕ)^269*50000000000000^205 ≤ 4976667948521^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1723336827 10000000000 4976667948521 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625775791/5000000000 : ℝ), (225347111/400000000 : ℝ), (-1723336827/10000000000 : ℝ)] ![(10737490894143/25000000000000 : ℝ), (47096700506939/100000000000000 : ℝ), (4976667948521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625775791/5000000000 : ℝ)|^269 ≤ (10737490894143/25000000000000 : ℝ)^205
        have hw : |(2625775791/5000000000 : ℝ)|=(2625775791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225347111/400000000 : ℝ)|^269 ≤ (47096700506939/100000000000000 : ℝ)^205
        have hw : |(225347111/400000000 : ℝ)|=(225347111/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1723336827/10000000000 : ℝ)|^269 ≤ (4976667948521/50000000000000 : ℝ)^205
        have hw : |(-1723336827/10000000000 : ℝ)|=(1723336827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s1_7 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (429306713/1000000000 : ℝ)*x 0 + (987962187/2000000000 : ℝ)*x 1 + (931941667/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429306713/1000000000 : ℝ)^269 ≤ (32970045041689/100000000000000 : ℝ)^205 := by
    have hnat : (429306713 : ℕ)^269*100000000000000^205 ≤ 32970045041689^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429306713 1000000000 32970045041689 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987962187/2000000000 : ℝ)^269 ≤ (39635850842803/100000000000000 : ℝ)^205 := by
    have hnat : (987962187 : ℕ)^269*100000000000000^205 ≤ 39635850842803^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987962187 2000000000 39635850842803 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931941667/2500000000 : ℝ)^269 ≤ (214016438319/781250000000 : ℝ)^205 := by
    have hnat : (931941667 : ℕ)^269*781250000000^205 ≤ 214016438319^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931941667 2500000000 214016438319 781250000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429306713/1000000000 : ℝ), (987962187/2000000000 : ℝ), (931941667/2500000000 : ℝ)] ![(32970045041689/100000000000000 : ℝ), (39635850842803/100000000000000 : ℝ), (214016438319/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429306713/1000000000 : ℝ)|^269 ≤ (32970045041689/100000000000000 : ℝ)^205
        have hw : |(429306713/1000000000 : ℝ)|=(429306713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(987962187/2000000000 : ℝ)|^269 ≤ (39635850842803/100000000000000 : ℝ)^205
        have hw : |(987962187/2000000000 : ℝ)|=(987962187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(931941667/2500000000 : ℝ)|^269 ≤ (214016438319/781250000000 : ℝ)^205
        have hw : |(931941667/2500000000 : ℝ)|=(931941667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1344_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26857/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1727/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19447/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26857/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26857/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26857/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26857/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26857/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26857/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1429/100000 : ℝ) ^ (4303/1024 : ℝ) ≤ (883367805587/50000000000000000000 : ℝ) := by
    have hpowers : (1429/100000 : ℝ)^4303 ≤ (883367805587/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1429 : ℕ)^4303*50000000000000000000^1024 ≤ 883367805587^1024*100000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1429 100000 883367805587 50000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1429/100000 : ℝ)) (X := (883367805587/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26857/100000 : ℝ) ^ (4303/1024 : ℝ) ≤ (398854836095913813/100000000000000000000 : ℝ) := by
    have hpowers : (26857/100000 : ℝ)^4303 ≤ (398854836095913813/100000000000000000000 : ℝ)^1024 := by
      have hnat : (26857 : ℕ)^4303*100000000000000000000^1024 ≤ 398854836095913813^1024*100000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26857 100000 398854836095913813 100000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26857/100000 : ℝ)) (X := (398854836095913813/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000883367805587/25000000000000000000 : ℝ) ≤ (10000000084087253/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (25000000883367805587/25000000000000000000 : ℝ)^1024 ≤ (10000000084087253/10000000000000000 : ℝ)^4303 := by
      have hnat : (25000000883367805587 : ℕ)^1024*10000000000000000^4303 ≤ 10000000084087253^4303*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000883367805587 25000000000000000000 10000000084087253 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000084087253/10000000000000000 : ℝ)) (X := (25000000883367805587/25000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100398856602831524987/100000000000000000000 : ℝ) ≤ (10009477339600297/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (100398856602831524987/100000000000000000000 : ℝ)^1024 ≤ (10009477339600297/10000000000000000 : ℝ)^4303 := by
      have hnat : (100398856602831524987 : ℕ)^1024*10000000000000000^4303 ≤ 10009477339600297^4303*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100398856602831524987 100000000000000000000 10009477339600297 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009477339600297/10000000000000000 : ℝ)) (X := (100398856602831524987/100000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50398854836095913813/50000000000000000000 : ℝ) ≤ (10018954595113341/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (50398854836095913813/50000000000000000000 : ℝ)^1024 ≤ (10018954595113341/10000000000000000 : ℝ)^4303 := by
      have hnat : (50398854836095913813 : ℕ)^1024*10000000000000000^4303 ≤ 10018954595113341^4303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50398854836095913813 50000000000000000000 10018954595113341 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018954595113341/10000000000000000 : ℝ)) (X := (50398854836095913813/50000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(883367805587/50000000000000000000 : ℝ) ≤ ((63563229035478597383/63570000000000000000 : ℝ)+2*(2369313878261/635700000000000 : ℝ)*(1429/100000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (63563229035478597383/63570000000000000000 : ℝ)+2*(2369313878261/635700000000000 : ℝ)*(1429/100000 : ℝ)=(10000000084087253/10000000000000000 : ℝ) by norm_num, show 1+2*(883367805587/50000000000000000000 : ℝ)=(25000000883367805587/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(398854836095913813/100000000000000000000 : ℝ)+(883367805587/50000000000000000000 : ℝ) ≤ ((63563229035478597383/63570000000000000000 : ℝ)+(2369313878261/635700000000000 : ℝ)*((26857/100000 : ℝ)+(1429/100000 : ℝ)))^(4303/1024 : ℝ) := by
    rw [show (63563229035478597383/63570000000000000000 : ℝ)+(2369313878261/635700000000000 : ℝ)*((26857/100000 : ℝ)+(1429/100000 : ℝ))=(10009477339600297/10000000000000000 : ℝ) by norm_num, show 1+(398854836095913813/100000000000000000000 : ℝ)+(883367805587/50000000000000000000 : ℝ)=(100398856602831524987/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(398854836095913813/100000000000000000000 : ℝ) ≤ ((63563229035478597383/63570000000000000000 : ℝ)+2*(2369313878261/635700000000000 : ℝ)*(26857/100000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (63563229035478597383/63570000000000000000 : ℝ)+2*(2369313878261/635700000000000 : ℝ)*(26857/100000 : ℝ)=(10018954595113341/10000000000000000 : ℝ) by norm_num, show 1+2*(398854836095913813/100000000000000000000 : ℝ)=(50398854836095913813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63563229035478597383/63570000000000000000 : ℝ)*(X 1 0+X 2 0)+(2369313878261/635700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1429/100000 : ℝ)) (hi := (26857/100000 : ℝ)) (c := (63563229035478597383/63570000000000000000 : ℝ)) (alpha := (2369313878261/635700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63563229035478597383/63570000000000000000 : ℝ)*(X 0 1+X 2 1)+(2369313878261/635700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1429/100000 : ℝ)) (hi := (26857/100000 : ℝ)) (c := (63563229035478597383/63570000000000000000 : ℝ)) (alpha := (2369313878261/635700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63563229035478597383/63570000000000000000 : ℝ)*(X 0 2+X 1 2)+(2369313878261/635700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1429/100000 : ℝ)) (hi := (26857/100000 : ℝ)) (c := (63563229035478597383/63570000000000000000 : ℝ)) (alpha := (2369313878261/635700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-498122293/2500000000 : ℝ)*X 0 0+(564124499/1000000000 : ℝ)*X 0 1+(2524010509/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2702755381/5000000000 : ℝ)*X 1 0+(-2308993687/10000000000 : ℝ)*X 1 1+(2524010567/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((270275537/500000000 : ℝ)*X 2 0+(2524010439/5000000000 : ℝ)*X 2 1+(-1154497021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4291949749/10000000000 : ℝ)*X 0 0+(3711905249/10000000000 : ℝ)*X 0 1+(4955389943/10000000000 : ℝ)*X 0 2+(4291949749/10000000000 : ℝ)*X 1 0+(3711905249/10000000000 : ℝ)*X 1 1+(4955389943/10000000000 : ℝ)*X 1 2+(4291949749/10000000000 : ℝ)*X 2 0+(3711905249/10000000000 : ℝ)*X 2 1+(4955389943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-398604431/2000000000 : ℝ)*X 0 0+(2527726673/5000000000 : ℝ)*X 0 1+(563367767/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251551681/10000000000 : ℝ)*X 1 0+(-86166839/500000000 : ℝ)*X 1 1+(5633677711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625775791/5000000000 : ℝ)*X 2 0+(225347111/400000000 : ℝ)*X 2 1+(-1723336827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((429306713/1000000000 : ℝ)*X 0 0+(987962187/2000000000 : ℝ)*X 0 1+(931941667/2500000000 : ℝ)*X 0 2+(429306713/1000000000 : ℝ)*X 1 0+(987962187/2000000000 : ℝ)*X 1 1+(931941667/2500000000 : ℝ)*X 1 2+(429306713/1000000000 : ℝ)*X 2 0+(987962187/2000000000 : ℝ)*X 2 1+(931941667/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93776842329311051265841/10595000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7561663/10000000000000 : ℝ)*(base1) + (1457623901/100000000000000 : ℝ)*(base19) + (362690789/25000000000000 : ℝ)*(base23) + (123044687/50000000000000 : ℝ)*(upper3) + (153847/156250000000 : ℝ)*(upper5) + (622480151045057/50000000000000 : ℝ)*(major0) + (622480151045057/50000000000000 : ℝ)*(major1) + (622480151045057/50000000000000 : ℝ)*(major2) + (1685713273575137/100000000000000 : ℝ)*(sp0) + (842859772674251/50000000000000 : ℝ)*(sp1) + (842859776104623/50000000000000 : ℝ)*(sp2) + (402097518759519/50000000000000 : ℝ)*(sp3) + (1561002779/20000000000000 : ℝ)*(sp4) + (524129657/12500000000000 : ℝ)*(sp7) + (201049826543231/25000000000000 : ℝ)*(f.failure) + (842860501486201/50000000000000 : ℝ)*(f.sum) + (99065858253149/31785000000000000000000000000 : ℝ)*base65 + (15896876361694014169/3178500000000000000000000000000000 : ℝ)*base68 + (5190593166079985831/3178500000000000000000000000000000 : ℝ)*base69 + (4754053868398014169/3178500000000000000000000000000000 : ℝ)*base72 + (6104512182713/15892500000000000000000000000 : ℝ)*base74 + (25360472296552014169/3178500000000000000000000000000000 : ℝ)*base76 + (9934673435995985831/3178500000000000000000000000000000 : ℝ)*base77 + (7024616742997985831/3178500000000000000000000000000000 : ℝ)*base79 + (25427202744101/7946250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4636023/2500000000000000000000 : ℝ)*base89 + (4636023/2500000000000000000000 : ℝ)*base91 + (4636023/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1324365161378340998523738609/132437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10944691/10000000000000 : ℝ)*(base1) + (2043054593/100000000000000 : ℝ)*(base19) + (401431981/20000000000000 : ℝ)*(base23) + (229830813/100000000000000 : ℝ)*(upper3) + (55487211/25000000000000 : ℝ)*(upper5) + (319310643131123/25000000000000 : ℝ)*(major0) + (319310643131123/25000000000000 : ℝ)*(major1) + (319310643131123/25000000000000 : ℝ)*(major2) + (5187890841/50000000000000 : ℝ)*(sp1) + (80183431/781250000000 : ℝ)*(sp2) + (432358109106939/25000000000000 : ℝ)*(sp4) + (1729419908144571/100000000000000 : ℝ)*(sp5) + (1729420056341773/100000000000000 : ℝ)*(sp6) + (165010475058073/20000000000000 : ℝ)*(sp7) + (33002099389491/4000000000000 : ℝ)*(f.failure) + (864716163490423/50000000000000 : ℝ)*(f.sum) + (5012565953231/15892500000000000000000000000 : ℝ)*base65 + (18443961419347798891/1589250000000000000000000000000000 : ℝ)*base68 + (2259755380258951109/1589250000000000000000000000000000 : ℝ)*base69 + (15450172213557298891/1589250000000000000000000000000000 : ℝ)*base72 + (92163963835973/31785000000000000000000000000 : ℝ)*base74 + (7226503057764298891/1589250000000000000000000000000000 : ℝ)*base76 + (24797447277694048891/1589250000000000000000000000000000 : ℝ)*base78 + (8874758199365548891/1589250000000000000000000000000000 : ℝ)*base80 + (180589982528407/31785000000000000000000000000 : ℝ)*base81 + (886603/400000000000000000000 : ℝ)*base89 + (886603/400000000000000000000 : ℝ)*base91 + (886603/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1344_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26857/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1727/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19447/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1344_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1344_s2_0 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2032470011/10000000000 : ℝ)*x 0 + (2739606257/5000000000 : ℝ)*x 1 + (5184440653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2032470011/10000000000 : ℝ)^269 ≤ (12359265457337/100000000000000 : ℝ)^205 := by
    have hnat : (2032470011 : ℕ)^269*100000000000000^205 ≤ 12359265457337^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032470011 10000000000 12359265457337 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739606257/5000000000 : ℝ)^269 ≤ (908191055179/2000000000000 : ℝ)^205 := by
    have hnat : (2739606257 : ℕ)^269*2000000000000^205 ≤ 908191055179^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739606257 5000000000 908191055179 2000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184440653/10000000000 : ℝ)^269 ≤ (1319724430301/3125000000000 : ℝ)^205 := by
    have hnat : (5184440653 : ℕ)^269*3125000000000^205 ≤ 1319724430301^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184440653 10000000000 1319724430301 3125000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2032470011/10000000000 : ℝ), (2739606257/5000000000 : ℝ), (5184440653/10000000000 : ℝ)] ![(12359265457337/100000000000000 : ℝ), (908191055179/2000000000000 : ℝ), (1319724430301/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2032470011/10000000000 : ℝ)|^269 ≤ (12359265457337/100000000000000 : ℝ)^205
        have hw : |(-2032470011/10000000000 : ℝ)|=(2032470011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739606257/5000000000 : ℝ)|^269 ≤ (908191055179/2000000000000 : ℝ)^205
        have hw : |(2739606257/5000000000 : ℝ)|=(2739606257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184440653/10000000000 : ℝ)|^269 ≤ (1319724430301/3125000000000 : ℝ)^205
        have hw : |(5184440653/10000000000 : ℝ)|=(5184440653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s2_1 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5365815147/10000000000 : ℝ)*x 0 + (-273095529/1250000000 : ℝ)*x 1 + (1036888209/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365815147/10000000000 : ℝ)^269 ≤ (1380636387771/3125000000000 : ℝ)^205 := by
    have hnat : (5365815147 : ℕ)^269*3125000000000^205 ≤ 1380636387771^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365815147 10000000000 1380636387771 3125000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273095529/1250000000 : ℝ)^269 ≤ (6794224809357/50000000000000 : ℝ)^205 := by
    have hnat : (273095529 : ℕ)^269*50000000000000^205 ≤ 6794224809357^205*1250000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273095529 1250000000 6794224809357 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036888209/2000000000 : ℝ)^269 ≤ (42231185959649/100000000000000 : ℝ)^205 := by
    have hnat : (1036888209 : ℕ)^269*100000000000000^205 ≤ 42231185959649^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036888209 2000000000 42231185959649 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365815147/10000000000 : ℝ), (-273095529/1250000000 : ℝ), (1036888209/2000000000 : ℝ)] ![(1380636387771/3125000000000 : ℝ), (6794224809357/50000000000000 : ℝ), (42231185959649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365815147/10000000000 : ℝ)|^269 ≤ (1380636387771/3125000000000 : ℝ)^205
        have hw : |(5365815147/10000000000 : ℝ)|=(5365815147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273095529/1250000000 : ℝ)|^269 ≤ (6794224809357/50000000000000 : ℝ)^205
        have hw : |(-273095529/1250000000 : ℝ)|=(273095529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036888209/2000000000 : ℝ)|^269 ≤ (42231185959649/100000000000000 : ℝ)^205
        have hw : |(1036888209/2000000000 : ℝ)|=(1036888209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s2_2 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (536581523/1000000000 : ℝ)*x 0 + (5184440949/10000000000 : ℝ)*x 1 + (-2184764247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536581523/1000000000 : ℝ)^269 ≤ (44180365305419/100000000000000 : ℝ)^205 := by
    have hnat : (536581523 : ℕ)^269*100000000000000^205 ≤ 44180365305419^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536581523 1000000000 44180365305419 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184440949/10000000000 : ℝ)^269 ≤ (21115592466761/50000000000000 : ℝ)^205 := by
    have hnat : (5184440949 : ℕ)^269*50000000000000^205 ≤ 21115592466761^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184440949 10000000000 21115592466761 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184764247/10000000000 : ℝ)^269 ≤ (2717689948227/20000000000000 : ℝ)^205 := by
    have hnat : (2184764247 : ℕ)^269*20000000000000^205 ≤ 2717689948227^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184764247 10000000000 2717689948227 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536581523/1000000000 : ℝ), (5184440949/10000000000 : ℝ), (-2184764247/10000000000 : ℝ)] ![(44180365305419/100000000000000 : ℝ), (21115592466761/50000000000000 : ℝ), (2717689948227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536581523/1000000000 : ℝ)|^269 ≤ (44180365305419/100000000000000 : ℝ)^205
        have hw : |(536581523/1000000000 : ℝ)|=(536581523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184440949/10000000000 : ℝ)|^269 ≤ (21115592466761/50000000000000 : ℝ)^205
        have hw : |(5184440949/10000000000 : ℝ)|=(5184440949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2184764247/10000000000 : ℝ)|^269 ≤ (2717689948227/20000000000000 : ℝ)^205
        have hw : |(-2184764247/10000000000 : ℝ)|=(2184764247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s2_3 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4319914087/10000000000 : ℝ)*x 0 + (4021260927/10000000000 : ℝ)*x 1 + (463914581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319914087/10000000000 : ℝ)^269 ≤ (1329634295971/4000000000000 : ℝ)^205 := by
    have hnat : (4319914087 : ℕ)^269*4000000000000^205 ≤ 1329634295971^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319914087 10000000000 1329634295971 4000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4021260927/10000000000 : ℝ)^269 ≤ (30258408356929/100000000000000 : ℝ)^205 := by
    have hnat : (4021260927 : ℕ)^269*100000000000000^205 ≤ 30258408356929^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021260927 10000000000 30258408356929 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (463914581/1000000000 : ℝ)^269 ≤ (36500734231047/100000000000000 : ℝ)^205 := by
    have hnat : (463914581 : ℕ)^269*100000000000000^205 ≤ 36500734231047^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463914581 1000000000 36500734231047 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319914087/10000000000 : ℝ), (4021260927/10000000000 : ℝ), (463914581/1000000000 : ℝ)] ![(1329634295971/4000000000000 : ℝ), (30258408356929/100000000000000 : ℝ), (36500734231047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319914087/10000000000 : ℝ)|^269 ≤ (1329634295971/4000000000000 : ℝ)^205
        have hw : |(4319914087/10000000000 : ℝ)|=(4319914087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4021260927/10000000000 : ℝ)|^269 ≤ (30258408356929/100000000000000 : ℝ)^205
        have hw : |(4021260927/10000000000 : ℝ)|=(4021260927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(463914581/1000000000 : ℝ)|^269 ≤ (36500734231047/100000000000000 : ℝ)^205
        have hw : |(463914581/1000000000 : ℝ)|=(463914581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s2_4 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2032535403/10000000000 : ℝ)*x 0 + (1037257179/2000000000 : ℝ)*x 1 + (219094027/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2032535403/10000000000 : ℝ)^269 ≤ (6179893622457/50000000000000 : ℝ)^205 := by
    have hnat : (2032535403 : ℕ)^269*50000000000000^205 ≤ 6179893622457^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032535403 10000000000 6179893622457 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037257179/2000000000 : ℝ)^269 ≤ (21125453162071/50000000000000 : ℝ)^205 := by
    have hnat : (1037257179 : ℕ)^269*50000000000000^205 ≤ 21125453162071^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037257179 2000000000 21125453162071 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219094027/400000000 : ℝ)^269 ≤ (5673663302033/12500000000000 : ℝ)^205 := by
    have hnat : (219094027 : ℕ)^269*12500000000000^205 ≤ 5673663302033^205*400000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219094027 400000000 5673663302033 12500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2032535403/10000000000 : ℝ), (1037257179/2000000000 : ℝ), (219094027/400000000 : ℝ)] ![(6179893622457/50000000000000 : ℝ), (21125453162071/50000000000000 : ℝ), (5673663302033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2032535403/10000000000 : ℝ)|^269 ≤ (6179893622457/50000000000000 : ℝ)^205
        have hw : |(-2032535403/10000000000 : ℝ)|=(2032535403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037257179/2000000000 : ℝ)|^269 ≤ (21125453162071/50000000000000 : ℝ)^205
        have hw : |(1037257179/2000000000 : ℝ)|=(1037257179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219094027/400000000 : ℝ)|^269 ≤ (5673663302033/12500000000000 : ℝ)^205
        have hw : |(219094027/400000000 : ℝ)|=(219094027/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s2_5 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5289821241/10000000000 : ℝ)*x 0 + (-1891854303/10000000000 : ℝ)*x 1 + (5477350669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289821241/10000000000 : ℝ)^269 ≤ (21680566635071/50000000000000 : ℝ)^205 := by
    have hnat : (5289821241 : ℕ)^269*50000000000000^205 ≤ 21680566635071^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289821241 10000000000 21680566635071 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1891854303/10000000000 : ℝ)^269 ≤ (5624780181827/50000000000000 : ℝ)^205 := by
    have hnat : (1891854303 : ℕ)^269*50000000000000^205 ≤ 5624780181827^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891854303 10000000000 5624780181827 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477350669/10000000000 : ℝ)^269 ≤ (45389306351021/100000000000000 : ℝ)^205 := by
    have hnat : (5477350669 : ℕ)^269*100000000000000^205 ≤ 45389306351021^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477350669 10000000000 45389306351021 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289821241/10000000000 : ℝ), (-1891854303/10000000000 : ℝ), (5477350669/10000000000 : ℝ)] ![(21680566635071/50000000000000 : ℝ), (5624780181827/50000000000000 : ℝ), (45389306351021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289821241/10000000000 : ℝ)|^269 ≤ (21680566635071/50000000000000 : ℝ)^205
        have hw : |(5289821241/10000000000 : ℝ)|=(5289821241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1891854303/10000000000 : ℝ)|^269 ≤ (5624780181827/50000000000000 : ℝ)^205
        have hw : |(-1891854303/10000000000 : ℝ)|=(1891854303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477350669/10000000000 : ℝ)|^269 ≤ (45389306351021/100000000000000 : ℝ)^205
        have hw : |(5477350669/10000000000 : ℝ)|=(5477350669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s2_6 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5289821251/10000000000 : ℝ)*x 0 + (2738675341/5000000000 : ℝ)*x 1 + (-1891854271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289821251/10000000000 : ℝ)^269 ≤ (5420141672213/12500000000000 : ℝ)^205 := by
    have hnat : (5289821251 : ℕ)^269*12500000000000^205 ≤ 5420141672213^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289821251 10000000000 5420141672213 12500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738675341/5000000000 : ℝ)^269 ≤ (2269465324619/5000000000000 : ℝ)^205 := by
    have hnat : (2738675341 : ℕ)^269*5000000000000^205 ≤ 2269465324619^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738675341 5000000000 2269465324619 5000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1891854271/10000000000 : ℝ)^269 ≤ (11249560113967/100000000000000 : ℝ)^205 := by
    have hnat : (1891854271 : ℕ)^269*100000000000000^205 ≤ 11249560113967^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891854271 10000000000 11249560113967 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289821251/10000000000 : ℝ), (2738675341/5000000000 : ℝ), (-1891854271/10000000000 : ℝ)] ![(5420141672213/12500000000000 : ℝ), (2269465324619/5000000000000 : ℝ), (11249560113967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289821251/10000000000 : ℝ)|^269 ≤ (5420141672213/12500000000000 : ℝ)^205
        have hw : |(5289821251/10000000000 : ℝ)|=(5289821251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738675341/5000000000 : ℝ)|^269 ≤ (2269465324619/5000000000000 : ℝ)^205
        have hw : |(2738675341/5000000000 : ℝ)|=(2738675341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1891854271/10000000000 : ℝ)|^269 ≤ (11249560113967/100000000000000 : ℝ)^205
        have hw : |(-1891854271/10000000000 : ℝ)|=(1891854271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s2_7 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (432005151/1000000000 : ℝ)*x 0 + (4635278557/10000000000 : ℝ)*x 1 + (4025163009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432005151/1000000000 : ℝ)^269 ≤ (1329689799053/4000000000000 : ℝ)^205 := by
    have hnat : (432005151 : ℕ)^269*4000000000000^205 ≤ 1329689799053^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432005151 1000000000 1329689799053 4000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4635278557/10000000000 : ℝ)^269 ≤ (4557601577549/12500000000000 : ℝ)^205 := by
    have hnat : (4635278557 : ℕ)^269*12500000000000^205 ≤ 4557601577549^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4635278557 10000000000 4557601577549 12500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4025163009/10000000000 : ℝ)^269 ≤ (1514847119207/5000000000000 : ℝ)^205 := by
    have hnat : (4025163009 : ℕ)^269*5000000000000^205 ≤ 1514847119207^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025163009 10000000000 1514847119207 5000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432005151/1000000000 : ℝ), (4635278557/10000000000 : ℝ), (4025163009/10000000000 : ℝ)] ![(1329689799053/4000000000000 : ℝ), (4557601577549/12500000000000 : ℝ), (1514847119207/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432005151/1000000000 : ℝ)|^269 ≤ (1329689799053/4000000000000 : ℝ)^205
        have hw : |(432005151/1000000000 : ℝ)|=(432005151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4635278557/10000000000 : ℝ)|^269 ≤ (4557601577549/12500000000000 : ℝ)^205
        have hw : |(4635278557/10000000000 : ℝ)|=(4635278557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4025163009/10000000000 : ℝ)|^269 ≤ (1514847119207/5000000000000 : ℝ)^205
        have hw : |(4025163009/10000000000 : ℝ)|=(4025163009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1344_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19447/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1973/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (503/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19447/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19447/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19447/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19447/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19447/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19447/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1727/25000 : ℝ) ^ (4303/1024 : ℝ) ≤ (331685289807507/25000000000000000000 : ℝ) := by
    have hpowers : (1727/25000 : ℝ)^4303 ≤ (331685289807507/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1727 : ℕ)^4303*25000000000000000000^1024 ≤ 331685289807507^1024*25000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1727 25000 331685289807507 25000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1727/25000 : ℝ)) (X := (331685289807507/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19447/100000 : ℝ) ^ (4303/1024 : ℝ) ≤ (20543910746542699/20000000000000000000 : ℝ) := by
    have hpowers : (19447/100000 : ℝ)^4303 ≤ (20543910746542699/20000000000000000000 : ℝ)^1024 := by
      have hnat : (19447 : ℕ)^4303*20000000000000000000^1024 ≤ 20543910746542699^1024*100000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19447 100000 20543910746542699 20000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19447/100000 : ℝ)) (X := (20543910746542699/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500331685289807507/12500000000000000000 : ℝ) ≤ (10000063145210869/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (12500331685289807507/12500000000000000000 : ℝ)^1024 ≤ (10000063145210869/10000000000000000 : ℝ)^4303 := by
      have hnat : (12500331685289807507 : ℕ)^1024*10000000000000000^4303 ≤ 10000063145210869^4303*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500331685289807507 12500000000000000000 10000063145210869 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063145210869/10000000000000000 : ℝ)) (X := (12500331685289807507/12500000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100104046294891943523/100000000000000000000 : ℝ) ≤ (10002475045195029/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (100104046294891943523/100000000000000000000 : ℝ)^1024 ≤ (10002475045195029/10000000000000000 : ℝ)^4303 := by
      have hnat : (100104046294891943523 : ℕ)^1024*10000000000000000^4303 ≤ 10002475045195029^4303*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100104046294891943523 100000000000000000000 10002475045195029 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002475045195029/10000000000000000 : ℝ)) (X := (100104046294891943523/100000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10020543910746542699/10000000000000000000 : ℝ) ≤ (10004886945179189/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (10020543910746542699/10000000000000000000 : ℝ)^1024 ≤ (10004886945179189/10000000000000000 : ℝ)^4303 := by
      have hnat : (10020543910746542699 : ℕ)^1024*10000000000000000^4303 ≤ 10004886945179189^4303*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10020543910746542699 10000000000000000000 10004886945179189 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004886945179189/10000000000000000 : ℝ)) (X := (10020543910746542699/10000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(331685289807507/25000000000000000000 : ℝ) ≤ ((125357468967617931831/125390000000000000000 : ℝ)+2*(15074374901/7836875000000 : ℝ)*(1727/25000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (125357468967617931831/125390000000000000000 : ℝ)+2*(15074374901/7836875000000 : ℝ)*(1727/25000 : ℝ)=(10000063145210869/10000000000000000 : ℝ) by norm_num, show 1+2*(331685289807507/25000000000000000000 : ℝ)=(12500331685289807507/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20543910746542699/20000000000000000000 : ℝ)+(331685289807507/25000000000000000000 : ℝ) ≤ ((125357468967617931831/125390000000000000000 : ℝ)+(15074374901/7836875000000 : ℝ)*((19447/100000 : ℝ)+(1727/25000 : ℝ)))^(4303/1024 : ℝ) := by
    rw [show (125357468967617931831/125390000000000000000 : ℝ)+(15074374901/7836875000000 : ℝ)*((19447/100000 : ℝ)+(1727/25000 : ℝ))=(10002475045195029/10000000000000000 : ℝ) by norm_num, show 1+(20543910746542699/20000000000000000000 : ℝ)+(331685289807507/25000000000000000000 : ℝ)=(100104046294891943523/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20543910746542699/20000000000000000000 : ℝ) ≤ ((125357468967617931831/125390000000000000000 : ℝ)+2*(15074374901/7836875000000 : ℝ)*(19447/100000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (125357468967617931831/125390000000000000000 : ℝ)+2*(15074374901/7836875000000 : ℝ)*(19447/100000 : ℝ)=(10004886945179189/10000000000000000 : ℝ) by norm_num, show 1+2*(20543910746542699/20000000000000000000 : ℝ)=(10020543910746542699/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (125357468967617931831/125390000000000000000 : ℝ)*(X 1 0+X 2 0)+(15074374901/7836875000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1727/25000 : ℝ)) (hi := (19447/100000 : ℝ)) (c := (125357468967617931831/125390000000000000000 : ℝ)) (alpha := (15074374901/7836875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (125357468967617931831/125390000000000000000 : ℝ)*(X 0 1+X 2 1)+(15074374901/7836875000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1727/25000 : ℝ)) (hi := (19447/100000 : ℝ)) (c := (125357468967617931831/125390000000000000000 : ℝ)) (alpha := (15074374901/7836875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (125357468967617931831/125390000000000000000 : ℝ)*(X 0 2+X 1 2)+(15074374901/7836875000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (1727/25000 : ℝ)) (hi := (19447/100000 : ℝ)) (c := (125357468967617931831/125390000000000000000 : ℝ)) (alpha := (15074374901/7836875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2032470011/10000000000 : ℝ)*X 0 0+(2739606257/5000000000 : ℝ)*X 0 1+(5184440653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5365815147/10000000000 : ℝ)*X 1 0+(-273095529/1250000000 : ℝ)*X 1 1+(1036888209/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536581523/1000000000 : ℝ)*X 2 0+(5184440949/10000000000 : ℝ)*X 2 1+(-2184764247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319914087/10000000000 : ℝ)*X 0 0+(4021260927/10000000000 : ℝ)*X 0 1+(463914581/1000000000 : ℝ)*X 0 2+(4319914087/10000000000 : ℝ)*X 1 0+(4021260927/10000000000 : ℝ)*X 1 1+(463914581/1000000000 : ℝ)*X 1 2+(4319914087/10000000000 : ℝ)*X 2 0+(4021260927/10000000000 : ℝ)*X 2 1+(463914581/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2032535403/10000000000 : ℝ)*X 0 0+(1037257179/2000000000 : ℝ)*X 0 1+(219094027/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289821241/10000000000 : ℝ)*X 1 0+(-1891854303/10000000000 : ℝ)*X 1 1+(5477350669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289821251/10000000000 : ℝ)*X 2 0+(2738675341/5000000000 : ℝ)*X 2 1+(-1891854271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((432005151/1000000000 : ℝ)*X 0 0+(4635278557/10000000000 : ℝ)*X 0 1+(4025163009/10000000000 : ℝ)*X 0 2+(432005151/1000000000 : ℝ)*X 1 0+(4635278557/10000000000 : ℝ)*X 1 1+(4025163009/10000000000 : ℝ)*X 1 2+(432005151/1000000000 : ℝ)*X 2 0+(4635278557/10000000000 : ℝ)*X 2 1+(4025163009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4760332930612119716825046273/1567375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223309121/50000000000000 : ℝ)*(base19) + (477490407/100000000000000 : ℝ)*(base23) + (72017677/100000000000000 : ℝ)*(upper3) + (11592087/100000000000000 : ℝ)*(upper4) + (54897749/100000000000000 : ℝ)*(upper5) + (626363039610513/25000000000000 : ℝ)*(major0) + (626363039610513/25000000000000 : ℝ)*(major1) + (626363039610513/25000000000000 : ℝ)*(major2) + (3392463357240583/100000000000000 : ℝ)*(sp0) + (1696236167319677/50000000000000 : ℝ)*(sp1) + (848118075941797/25000000000000 : ℝ)*(sp2) + (1618427765626591/100000000000000 : ℝ)*(sp3) + (2356004253/25000000000000 : ℝ)*(sp4) + (917190499/25000000000000 : ℝ)*(sp7) + (1618431434388587/100000000000000 : ℝ)*(f.failure) + (678494556251519/20000000000000 : ℝ)*(f.sum) + (3042762014591/1567375000000000000000000000 : ℝ)*base66 + (44471336943805689303/3134750000000000000000000000000000 : ℝ)*base67 + (50233908866246189303/3134750000000000000000000000000000 : ℝ)*base69 + (22162056656311689303/3134750000000000000000000000000000 : ℝ)*base71 + (1961508284809/501560000000000000000000000 : ℝ)*base73 + (19345395415843939303/3134750000000000000000000000000000 : ℝ)*base75 + (36992000287592189303/3134750000000000000000000000000000 : ℝ)*base77 + (50828986082458189303/3134750000000000000000000000000000 : ℝ)*base79 + (15645826213491/6269500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (122032829/10000000000000000000000 : ℝ)*base90 + (122032829/10000000000000000000000 : ℝ)*base92 + (122032829/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (563852076428128937488151151/156737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (406301673/50000000000000 : ℝ)*(base19) + (950809787/100000000000000 : ℝ)*(base23) + (102542069/100000000000000 : ℝ)*(upper3) + (24721291/50000000000000 : ℝ)*(lower4) + (33948429/100000000000000 : ℝ)*(upper5) + (126867342161407/5000000000000 : ℝ)*(major0) + (126867342161407/5000000000000 : ℝ)*(major1) + (126867342161407/5000000000000 : ℝ)*(major2) + (4487878031/50000000000000 : ℝ)*(sp1) + (11637865793/100000000000000 : ℝ)*(sp2) + (1717829659946503/50000000000000 : ℝ)*(sp4) + (3435649531533597/100000000000000 : ℝ)*(sp5) + (1717823365608713/50000000000000 : ℝ)*(sp6) + (819517123324479/50000000000000 : ℝ)*(sp7) + (819517123324479/50000000000000 : ℝ)*(f.failure) + (1717829659946503/50000000000000 : ℝ)*(f.sum) + (11969007528081/6269500000000000000000000000 : ℝ)*base65 + (4061398248716153783/626950000000000000000000000000000 : ℝ)*base68 + (3180364031623353783/626950000000000000000000000000000 : ℝ)*base70 + (897675381401403783/626950000000000000000000000000000 : ℝ)*base72 + (43313702063071/12539000000000000000000000000 : ℝ)*base73 + (253809681592296217/626950000000000000000000000000000 : ℝ)*base75 + (5887785052060153783/626950000000000000000000000000000 : ℝ)*base78 + (7359150056943203783/626950000000000000000000000000000 : ℝ)*base80 + (7218087178617/2507800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (20052407/5000000000000000000000 : ℝ)*base89 + (20052407/5000000000000000000000 : ℝ)*base91 + (20052407/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1344_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19447/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1973/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (503/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1344_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1344_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1973/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (503/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1344_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1344_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1344_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1973/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (503/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1344_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

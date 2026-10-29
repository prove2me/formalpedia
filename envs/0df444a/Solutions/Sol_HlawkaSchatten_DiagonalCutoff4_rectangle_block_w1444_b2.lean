-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1444_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:57:33.21399+00:00
-- url     : https://prove2.me/submissions/ea17ce88-313d-4e13-9516-5ef7cb3c63af

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
theorem support_rectangle_w1444_s6_0 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-489756007/2500000000 : ℝ)*x 0 + (1351862207/2500000000 : ℝ)*x 1 + (5247229187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489756007/2500000000 : ℝ)^1101 ≤ (5977603975239/50000000000000 : ℝ)^845 := by
    have hnat : (489756007 : ℕ)^1101*50000000000000^845 ≤ 5977603975239^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489756007 2500000000 5977603975239 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351862207/2500000000 : ℝ)^1101 ≤ (44884891585053/100000000000000 : ℝ)^845 := by
    have hnat : (1351862207 : ℕ)^1101*100000000000000^845 ≤ 44884891585053^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351862207 2500000000 44884891585053 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247229187/10000000000 : ℝ)^1101 ≤ (1726396018093/4000000000000 : ℝ)^845 := by
    have hnat : (5247229187 : ℕ)^1101*4000000000000^845 ≤ 1726396018093^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247229187 10000000000 1726396018093 4000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489756007/2500000000 : ℝ), (1351862207/2500000000 : ℝ), (5247229187/10000000000 : ℝ)] ![(5977603975239/50000000000000 : ℝ), (44884891585053/100000000000000 : ℝ), (1726396018093/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489756007/2500000000 : ℝ)|^1101 ≤ (5977603975239/50000000000000 : ℝ)^845
        have hw : |(-489756007/2500000000 : ℝ)|=(489756007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351862207/2500000000 : ℝ)|^1101 ≤ (44884891585053/100000000000000 : ℝ)^845
        have hw : |(1351862207/2500000000 : ℝ)|=(1351862207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247229187/10000000000 : ℝ)|^1101 ≤ (1726396018093/4000000000000 : ℝ)^845
        have hw : |(5247229187/10000000000 : ℝ)|=(5247229187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s6_1 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673504001/5000000000 : ℝ)*x 0 + (-1020292131/5000000000 : ℝ)*x 1 + (5247229191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673504001/5000000000 : ℝ)^1101 ≤ (8846463176577/20000000000000 : ℝ)^845 := by
    have hnat : (2673504001 : ℕ)^1101*20000000000000^845 ≤ 8846463176577^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673504001 5000000000 8846463176577 20000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020292131/5000000000 : ℝ)^1101 ≤ (787986475641/6250000000000 : ℝ)^845 := by
    have hnat : (1020292131 : ℕ)^1101*6250000000000^845 ≤ 787986475641^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020292131 5000000000 787986475641 6250000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247229191/10000000000 : ℝ)^1101 ≤ (21579950247597/50000000000000 : ℝ)^845 := by
    have hnat : (5247229191 : ℕ)^1101*50000000000000^845 ≤ 21579950247597^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247229191 10000000000 21579950247597 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673504001/5000000000 : ℝ), (-1020292131/5000000000 : ℝ), (5247229191/10000000000 : ℝ)] ![(8846463176577/20000000000000 : ℝ), (787986475641/6250000000000 : ℝ), (21579950247597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673504001/5000000000 : ℝ)|^1101 ≤ (8846463176577/20000000000000 : ℝ)^845
        have hw : |(2673504001/5000000000 : ℝ)|=(2673504001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1020292131/5000000000 : ℝ)|^1101 ≤ (787986475641/6250000000000 : ℝ)^845
        have hw : |(-1020292131/5000000000 : ℝ)|=(1020292131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247229191/10000000000 : ℝ)|^1101 ≤ (21579950247597/50000000000000 : ℝ)^845
        have hw : |(5247229191/10000000000 : ℝ)|=(5247229191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s6_2 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347008001/10000000000 : ℝ)*x 0 + (5247229189/10000000000 : ℝ)*x 1 + (-1020292133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347008001/10000000000 : ℝ)^1101 ≤ (44232315872107/100000000000000 : ℝ)^845 := by
    have hnat : (5347008001 : ℕ)^1101*100000000000000^845 ≤ 44232315872107^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347008001 10000000000 44232315872107 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247229189/10000000000 : ℝ)^1101 ≤ (269749377961/625000000000 : ℝ)^845 := by
    have hnat : (5247229189 : ℕ)^1101*625000000000^845 ≤ 269749377961^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247229189 10000000000 269749377961 625000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020292133/5000000000 : ℝ)^1101 ≤ (12607783642457/100000000000000 : ℝ)^845 := by
    have hnat : (1020292133 : ℕ)^1101*100000000000000^845 ≤ 12607783642457^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020292133 5000000000 12607783642457 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347008001/10000000000 : ℝ), (5247229189/10000000000 : ℝ), (-1020292133/5000000000 : ℝ)] ![(44232315872107/100000000000000 : ℝ), (269749377961/625000000000 : ℝ), (12607783642457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347008001/10000000000 : ℝ)|^1101 ≤ (44232315872107/100000000000000 : ℝ)^845
        have hw : |(5347008001/10000000000 : ℝ)|=(5347008001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247229189/10000000000 : ℝ)|^1101 ≤ (269749377961/625000000000 : ℝ)^845
        have hw : |(5247229189/10000000000 : ℝ)|=(5247229189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020292133/5000000000 : ℝ)|^1101 ≤ (12607783642457/100000000000000 : ℝ)^845
        have hw : |(-1020292133/5000000000 : ℝ)|=(1020292133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s6_3 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2150318253/5000000000 : ℝ)*x 0 + (4129534257/10000000000 : ℝ)*x 1 + (55975609/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150318253/5000000000 : ℝ)^1101 ≤ (16652457729103/50000000000000 : ℝ)^845 := by
    have hnat : (2150318253 : ℕ)^1101*50000000000000^845 ≤ 16652457729103^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150318253 5000000000 16652457729103 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129534257/10000000000 : ℝ)^1101 ≤ (6317787343351/20000000000000 : ℝ)^845 := by
    have hnat : (4129534257 : ℕ)^1101*20000000000000^845 ≤ 6317787343351^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129534257 10000000000 6317787343351 20000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55975609/125000000 : ℝ)^1101 ≤ (1404245912103/4000000000000 : ℝ)^845 := by
    have hnat : (55975609 : ℕ)^1101*4000000000000^845 ≤ 1404245912103^845*125000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55975609 125000000 1404245912103 4000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150318253/5000000000 : ℝ), (4129534257/10000000000 : ℝ), (55975609/125000000 : ℝ)] ![(16652457729103/50000000000000 : ℝ), (6317787343351/20000000000000 : ℝ), (1404245912103/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150318253/5000000000 : ℝ)|^1101 ≤ (16652457729103/50000000000000 : ℝ)^845
        have hw : |(2150318253/5000000000 : ℝ)|=(2150318253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129534257/10000000000 : ℝ)|^1101 ≤ (6317787343351/20000000000000 : ℝ)^845
        have hw : |(4129534257/10000000000 : ℝ)|=(4129534257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(55975609/125000000 : ℝ)|^1101 ≤ (1404245912103/4000000000000 : ℝ)^845
        have hw : |(55975609/125000000 : ℝ)|=(55975609/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s6_4 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1959035221/10000000000 : ℝ)*x 0 + (131195193/250000000 : ℝ)*x 1 + (2703433647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1959035221/10000000000 : ℝ)^1101 ≤ (11955296951473/100000000000000 : ℝ)^845 := by
    have hnat : (1959035221 : ℕ)^1101*100000000000000^845 ≤ 11955296951473^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959035221 10000000000 11955296951473 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131195193/250000000 : ℝ)^1101 ≤ (10791525201277/25000000000000 : ℝ)^845 := by
    have hnat : (131195193 : ℕ)^1101*25000000000000^845 ≤ 10791525201277^845*250000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131195193 250000000 10791525201277 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703433647/5000000000 : ℝ)^1101 ≤ (44878602225717/100000000000000 : ℝ)^845 := by
    have hnat : (2703433647 : ℕ)^1101*100000000000000^845 ≤ 44878602225717^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703433647 5000000000 44878602225717 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1959035221/10000000000 : ℝ), (131195193/250000000 : ℝ), (2703433647/5000000000 : ℝ)] ![(11955296951473/100000000000000 : ℝ), (10791525201277/25000000000000 : ℝ), (44878602225717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1959035221/10000000000 : ℝ)|^1101 ≤ (11955296951473/100000000000000 : ℝ)^845
        have hw : |(-1959035221/10000000000 : ℝ)|=(1959035221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131195193/250000000 : ℝ)|^1101 ≤ (10791525201277/25000000000000 : ℝ)^845
        have hw : |(131195193/250000000 : ℝ)|=(131195193/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703433647/5000000000 : ℝ)|^1101 ≤ (44878602225717/100000000000000 : ℝ)^845
        have hw : |(2703433647/5000000000 : ℝ)|=(2703433647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s6_5 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305294869/10000000000 : ℝ)*x 0 + (-37618923/200000000 : ℝ)*x 1 + (5406867207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305294869/10000000000 : ℝ)^1101 ≤ (8756648397271/20000000000000 : ℝ)^845 := by
    have hnat : (5305294869 : ℕ)^1101*20000000000000^845 ≤ 8756648397271^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305294869 10000000000 8756648397271 20000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37618923/200000000 : ℝ)^1101 ≤ (177158698637/1562500000000 : ℝ)^845 := by
    have hnat : (37618923 : ℕ)^1101*1562500000000^845 ≤ 177158698637^845*200000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37618923 200000000 177158698637 1562500000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406867207/10000000000 : ℝ)^1101 ≤ (44878601284817/100000000000000 : ℝ)^845 := by
    have hnat : (5406867207 : ℕ)^1101*100000000000000^845 ≤ 44878601284817^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406867207 10000000000 44878601284817 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305294869/10000000000 : ℝ), (-37618923/200000000 : ℝ), (5406867207/10000000000 : ℝ)] ![(8756648397271/20000000000000 : ℝ), (177158698637/1562500000000 : ℝ), (44878601284817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305294869/10000000000 : ℝ)|^1101 ≤ (8756648397271/20000000000000 : ℝ)^845
        have hw : |(5305294869/10000000000 : ℝ)|=(5305294869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37618923/200000000 : ℝ)|^1101 ≤ (177158698637/1562500000000 : ℝ)^845
        have hw : |(-37618923/200000000 : ℝ)|=(37618923/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406867207/10000000000 : ℝ)|^1101 ≤ (44878601284817/100000000000000 : ℝ)^845
        have hw : |(5406867207/10000000000 : ℝ)|=(5406867207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s6_6 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (331580943/625000000 : ℝ)*x 0 + (5406866901/10000000000 : ℝ)*x 1 + (-58779571/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331580943/625000000 : ℝ)^1101 ≤ (43783244341259/100000000000000 : ℝ)^845 := by
    have hnat : (331580943 : ℕ)^1101*100000000000000^845 ≤ 43783244341259^845*625000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331580943 625000000 43783244341259 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406866901/10000000000 : ℝ)^1101 ≤ (11219649493861/25000000000000 : ℝ)^845 := by
    have hnat : (5406866901 : ℕ)^1101*25000000000000^845 ≤ 11219649493861^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406866901 10000000000 11219649493861 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58779571/312500000 : ℝ)^1101 ≤ (11338157670969/100000000000000 : ℝ)^845 := by
    have hnat : (58779571 : ℕ)^1101*100000000000000^845 ≤ 11338157670969^845*312500000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58779571 312500000 11338157670969 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331580943/625000000 : ℝ), (5406866901/10000000000 : ℝ), (-58779571/312500000 : ℝ)] ![(43783244341259/100000000000000 : ℝ), (11219649493861/25000000000000 : ℝ), (11338157670969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331580943/625000000 : ℝ)|^1101 ≤ (43783244341259/100000000000000 : ℝ)^845
        have hw : |(331580943/625000000 : ℝ)|=(331580943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406866901/10000000000 : ℝ)|^1101 ≤ (11219649493861/25000000000000 : ℝ)^845
        have hw : |(5406866901/10000000000 : ℝ)|=(5406866901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58779571/312500000 : ℝ)|^1101 ≤ (11338157670969/100000000000000 : ℝ)^845
        have hw : |(-58779571/312500000 : ℝ)|=(58779571/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s6_7 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4300660943/10000000000 : ℝ)*x 0 + (4476789899/10000000000 : ℝ)*x 1 + (1032699877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300660943/10000000000 : ℝ)^1101 ≤ (520393156817/1562500000000 : ℝ)^845 := by
    have hnat : (4300660943 : ℕ)^1101*1562500000000^845 ≤ 520393156817^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300660943 10000000000 520393156817 1562500000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476789899/10000000000 : ℝ)^1101 ≤ (1096665309073/3125000000000 : ℝ)^845 := by
    have hnat : (4476789899 : ℕ)^1101*3125000000000^845 ≤ 1096665309073^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476789899 10000000000 1096665309073 3125000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032699877/2500000000 : ℝ)^1101 ≤ (15800774030613/50000000000000 : ℝ)^845 := by
    have hnat : (1032699877 : ℕ)^1101*50000000000000^845 ≤ 15800774030613^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032699877 2500000000 15800774030613 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300660943/10000000000 : ℝ), (4476789899/10000000000 : ℝ), (1032699877/2500000000 : ℝ)] ![(520393156817/1562500000000 : ℝ), (1096665309073/3125000000000 : ℝ), (15800774030613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300660943/10000000000 : ℝ)|^1101 ≤ (520393156817/1562500000000 : ℝ)^845
        have hw : |(4300660943/10000000000 : ℝ)|=(4300660943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476789899/10000000000 : ℝ)|^1101 ≤ (1096665309073/3125000000000 : ℝ)^845
        have hw : |(4476789899/10000000000 : ℝ)|=(4476789899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032699877/2500000000 : ℝ)|^1101 ≤ (15800774030613/50000000000000 : ℝ)^845
        have hw : |(1032699877/2500000000 : ℝ)|=(1032699877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1444_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1137/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2953/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11367/100000 : ℝ) ^ (4403/1024 : ℝ) ≤ (8698845995288113/100000000000000000000 : ℝ) := by
    have hpowers : (11367/100000 : ℝ)^4403 ≤ (8698845995288113/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11367 : ℕ)^4403*100000000000000000000^1024 ≤ 8698845995288113^1024*100000^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11367 100000 8698845995288113 100000000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11367/100000 : ℝ)) (X := (8698845995288113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (923/6250 : ℝ) ^ (4403/1024 : ℝ) ≤ (214454650611779/800000000000000000 : ℝ) := by
    have hpowers : (923/6250 : ℝ)^4403 ≤ (214454650611779/800000000000000000 : ℝ)^1024 := by
      have hnat : (923 : ℕ)^4403*800000000000000000^1024 ≤ 214454650611779^1024*6250^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 6250 214454650611779 800000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/6250 : ℝ)) (X := (214454650611779/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008698845995288113/50000000000000000000 : ℝ) ≤ (400016183554319/400000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (50008698845995288113/50000000000000000000 : ℝ)^1024 ≤ (400016183554319/400000000000000 : ℝ)^4403 := by
      have hnat : (50008698845995288113 : ℕ)^1024*400000000000000^4403 ≤ 400016183554319^4403*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008698845995288113 50000000000000000000 400016183554319 400000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400016183554319/400000000000000 : ℝ)) (X := (50008698845995288113/50000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504438209665220061/12500000000000000000 : ℝ) ≤ (1000082563845547/1000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (12504438209665220061/12500000000000000000 : ℝ)^1024 ≤ (1000082563845547/1000000000000000 : ℝ)^4403 := by
      have hnat : (12504438209665220061 : ℕ)^1024*1000000000000000^4403 ≤ 1000082563845547^4403*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504438209665220061 12500000000000000000 1000082563845547 1000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000082563845547/1000000000000000 : ℝ)) (X := (12504438209665220061/12500000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400214454650611779/400000000000000000 : ℝ) ≤ (2000249337610593/2000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (400214454650611779/400000000000000000 : ℝ)^1024 ≤ (2000249337610593/2000000000000000 : ℝ)^4403 := by
      have hnat : (400214454650611779 : ℕ)^1024*2000000000000000^4403 ≤ 2000249337610593^4403*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400214454650611779 400000000000000000 2000249337610593 2000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000249337610593/2000000000000000 : ℝ)) (X := (400214454650611779/400000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8698845995288113/100000000000000000000 : ℝ) ≤ ((6800360773031304329/6802000000000000000 : ℝ)+2*(84209919499/68020000000000 : ℝ)*(11367/100000 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (6800360773031304329/6802000000000000000 : ℝ)+2*(84209919499/68020000000000 : ℝ)*(11367/100000 : ℝ)=(400016183554319/400000000000000 : ℝ) by norm_num, show 1+2*(8698845995288113/100000000000000000000 : ℝ)=(50008698845995288113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(214454650611779/800000000000000000 : ℝ)+(8698845995288113/100000000000000000000 : ℝ) ≤ ((6800360773031304329/6802000000000000000 : ℝ)+(84209919499/68020000000000 : ℝ)*((923/6250 : ℝ)+(11367/100000 : ℝ)))^(4403/1024 : ℝ) := by
    rw [show (6800360773031304329/6802000000000000000 : ℝ)+(84209919499/68020000000000 : ℝ)*((923/6250 : ℝ)+(11367/100000 : ℝ))=(1000082563845547/1000000000000000 : ℝ) by norm_num, show 1+(214454650611779/800000000000000000 : ℝ)+(8698845995288113/100000000000000000000 : ℝ)=(12504438209665220061/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(214454650611779/800000000000000000 : ℝ) ≤ ((6800360773031304329/6802000000000000000 : ℝ)+2*(84209919499/68020000000000 : ℝ)*(923/6250 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (6800360773031304329/6802000000000000000 : ℝ)+2*(84209919499/68020000000000 : ℝ)*(923/6250 : ℝ)=(2000249337610593/2000000000000000 : ℝ) by norm_num, show 1+2*(214454650611779/800000000000000000 : ℝ)=(400214454650611779/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6800360773031304329/6802000000000000000 : ℝ)*(X 1 0+X 2 0)+(84209919499/68020000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (6800360773031304329/6802000000000000000 : ℝ)) (alpha := (84209919499/68020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6800360773031304329/6802000000000000000 : ℝ)*(X 0 1+X 2 1)+(84209919499/68020000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (6800360773031304329/6802000000000000000 : ℝ)) (alpha := (84209919499/68020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6800360773031304329/6802000000000000000 : ℝ)*(X 0 2+X 1 2)+(84209919499/68020000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (6800360773031304329/6802000000000000000 : ℝ)) (alpha := (84209919499/68020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-489756007/2500000000 : ℝ)*X 0 0+(1351862207/2500000000 : ℝ)*X 0 1+(5247229187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673504001/5000000000 : ℝ)*X 1 0+(-1020292131/5000000000 : ℝ)*X 1 1+(5247229191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347008001/10000000000 : ℝ)*X 2 0+(5247229189/10000000000 : ℝ)*X 2 1+(-1020292133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150318253/5000000000 : ℝ)*X 0 0+(4129534257/10000000000 : ℝ)*X 0 1+(55975609/125000000 : ℝ)*X 0 2+(2150318253/5000000000 : ℝ)*X 1 0+(4129534257/10000000000 : ℝ)*X 1 1+(55975609/125000000 : ℝ)*X 1 2+(2150318253/5000000000 : ℝ)*X 2 0+(4129534257/10000000000 : ℝ)*X 2 1+(55975609/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1959035221/10000000000 : ℝ)*X 0 0+(131195193/250000000 : ℝ)*X 0 1+(2703433647/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305294869/10000000000 : ℝ)*X 1 0+(-37618923/200000000 : ℝ)*X 1 1+(5406867207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331580943/625000000 : ℝ)*X 2 0+(5406866901/10000000000 : ℝ)*X 2 1+(-58779571/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300660943/10000000000 : ℝ)*X 0 0+(4476789899/10000000000 : ℝ)*X 0 1+(1032699877/2500000000 : ℝ)*X 0 2+(4300660943/10000000000 : ℝ)*X 1 0+(4476789899/10000000000 : ℝ)*X 1 1+(1032699877/2500000000 : ℝ)*X 1 2+(4300660943/10000000000 : ℝ)*X 2 0+(4476789899/10000000000 : ℝ)*X 2 1+(1032699877/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34061770880265888316017/3401000000000000000000000000 : ℝ) := by norm_num
    linear_combination (904522319/50000000000000 : ℝ)*(base19) + (1683851659/100000000000000 : ℝ)*(base23) + (13263327/20000000000000 : ℝ)*(lower2) + (25281767/10000000000000 : ℝ)*(upper3) + (39371019/25000000000000 : ℝ)*(upper5) + (4555434024906207/100000000000000 : ℝ)*(major0) + (4555434024906207/100000000000000 : ℝ)*(major1) + (4555434024906207/100000000000000 : ℝ)*(major2) + (6241472095894127/100000000000000 : ℝ)*(sp0) + (249660338619097/4000000000000 : ℝ)*(sp1) + (1560377147667601/25000000000000 : ℝ)*(sp2) + (1434669188203271/50000000000000 : ℝ)*(sp3) + (1193082123/3125000000000 : ℝ)*(sp4) + (9532521531/50000000000000 : ℝ)*(sp7) + (717339360362401/25000000000000 : ℝ)*(f.failure) + (6241510274522063/100000000000000 : ℝ)*(f.sum) + (558797742413/3401000000000000000000000000 : ℝ)*base66 + (3360525470865770103/680200000000000000000000000000000 : ℝ)*base67 + (1957965512726429897/680200000000000000000000000000000 : ℝ)*base70 + (1088953044973770103/680200000000000000000000000000000 : ℝ)*base71 + (473508743189/3401000000000000000000000000 : ℝ)*base74 + (54836137934829897/680200000000000000000000000000000 : ℝ)*base76 + (214682601257029897/680200000000000000000000000000000 : ℝ)*base78 + (136021535809770103/680200000000000000000000000000000 : ℝ)*base79 + (8441799229221/3401000000000000000000000000 : ℝ)*base81 + (19872931/2500000000000000000000 : ℝ)*base90 + (19872931/2500000000000000000000 : ℝ)*base92 + (19872931/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92663255889230462433/9500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2003031911/100000000000000 : ℝ)*(base19) + (298729851/12500000000000 : ℝ)*(base23) + (648896773/100000000000000 : ℝ)*(lower1) + (8025677/6250000000000 : ℝ)*(upper3) + (11315909/12500000000000 : ℝ)*(lower4) + (300977937/100000000000000 : ℝ)*(upper5) + (4588575360313233/100000000000000 : ℝ)*(major0) + (4588575360313233/100000000000000 : ℝ)*(major1) + (4588575360313233/100000000000000 : ℝ)*(major2) + (5513433811/100000000000000 : ℝ)*(sp1) + (98233094225203/1562500000000 : ℝ)*(sp4) + (6286910513947269/100000000000000 : ℝ)*(sp5) + (785864455071773/12500000000000 : ℝ)*(sp6) + (45159880704363/1562500000000 : ℝ)*(sp7) + (45159880704363/1562500000000 : ℝ)*(f.failure) + (98233094225203/1562500000000 : ℝ)*(f.sum) + (24472760537/19000000000000000000000000 : ℝ)*base65 + (37822114936234717/3800000000000000000000000000000 : ℝ)*base68 + (2650552581034717/3800000000000000000000000000000 : ℝ)*base70 + (25075567329965283/3800000000000000000000000000000 : ℝ)*base71 + (75459377111/19000000000000000000000000 : ℝ)*base74 + (9314123862165283/3800000000000000000000000000000 : ℝ)*base75 + (757553944234717/3800000000000000000000000000000 : ℝ)*base78 + (23362499996565283/3800000000000000000000000000000 : ℝ)*base79 + (69264333479/19000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1973253/156250000000000000000 : ℝ)*base90 + (1973253/156250000000000000000 : ℝ)*base92 + (1973253/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1444_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1444_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1444_s7_0 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1959027147/10000000000 : ℝ)*x 0 + (5407427643/10000000000 : ℝ)*x 1 + (5247248251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1959027147/10000000000 : ℝ)^1101 ≤ (11955232751151/100000000000000 : ℝ)^845 := by
    have hnat : (1959027147 : ℕ)^1101*100000000000000^845 ≤ 11955232751151^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959027147 10000000000 11955232751151 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407427643/10000000000 : ℝ)^1101 ≤ (44884662463163/100000000000000 : ℝ)^845 := by
    have hnat : (5407427643 : ℕ)^1101*100000000000000^845 ≤ 44884662463163^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407427643 10000000000 44884662463163 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247248251/10000000000 : ℝ)^1101 ≤ (21580052382493/50000000000000 : ℝ)^845 := by
    have hnat : (5247248251 : ℕ)^1101*50000000000000^845 ≤ 21580052382493^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247248251 10000000000 21580052382493 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1959027147/10000000000 : ℝ), (5407427643/10000000000 : ℝ), (5247248251/10000000000 : ℝ)] ![(11955232751151/100000000000000 : ℝ), (44884662463163/100000000000000 : ℝ), (21580052382493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1959027147/10000000000 : ℝ)|^1101 ≤ (11955232751151/100000000000000 : ℝ)^845
        have hw : |(-1959027147/10000000000 : ℝ)|=(1959027147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407427643/10000000000 : ℝ)|^1101 ≤ (44884662463163/100000000000000 : ℝ)^845
        have hw : |(5407427643/10000000000 : ℝ)|=(5407427643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247248251/10000000000 : ℝ)|^1101 ≤ (21580052382493/50000000000000 : ℝ)^845
        have hw : |(5247248251/10000000000 : ℝ)|=(5247248251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s7_1 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673501699/5000000000 : ℝ)*x 0 + (-2040565741/10000000000 : ℝ)*x 1 + (2623623867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673501699/5000000000 : ℝ)^1101 ≤ (44232266258549/100000000000000 : ℝ)^845 := by
    have hnat : (2673501699 : ℕ)^1101*100000000000000^845 ≤ 44232266258549^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673501699 5000000000 44232266258549 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040565741/10000000000 : ℝ)^1101 ≤ (3151908627477/25000000000000 : ℝ)^845 := by
    have hnat : (2040565741 : ℕ)^1101*25000000000000^845 ≤ 3151908627477^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040565741 10000000000 3151908627477 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623623867/5000000000 : ℝ)^1101 ≤ (337188275189/781250000000 : ℝ)^845 := by
    have hnat : (2623623867 : ℕ)^1101*781250000000^845 ≤ 337188275189^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623623867 5000000000 337188275189 781250000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673501699/5000000000 : ℝ), (-2040565741/10000000000 : ℝ), (2623623867/5000000000 : ℝ)] ![(44232266258549/100000000000000 : ℝ), (3151908627477/25000000000000 : ℝ), (337188275189/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673501699/5000000000 : ℝ)|^1101 ≤ (44232266258549/100000000000000 : ℝ)^845
        have hw : |(2673501699/5000000000 : ℝ)|=(2673501699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2040565741/10000000000 : ℝ)|^1101 ≤ (3151908627477/25000000000000 : ℝ)^845
        have hw : |(-2040565741/10000000000 : ℝ)|=(2040565741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623623867/5000000000 : ℝ)|^1101 ≤ (337188275189/781250000000 : ℝ)^845
        have hw : |(2623623867/5000000000 : ℝ)|=(2623623867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s7_2 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534700261/1000000000 : ℝ)*x 0 + (1311812287/2500000000 : ℝ)*x 1 + (-2040564913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534700261/1000000000 : ℝ)^1101 ≤ (44232257765071/100000000000000 : ℝ)^845 := by
    have hnat : (534700261 : ℕ)^1101*100000000000000^845 ≤ 44232257765071^845*1000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534700261 1000000000 44232257765071 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311812287/2500000000 : ℝ)^1101 ≤ (21580057189159/50000000000000 : ℝ)^845 := by
    have hnat : (1311812287 : ℕ)^1101*50000000000000^845 ≤ 21580057189159^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311812287 2500000000 21580057189159 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2040564913/10000000000 : ℝ)^1101 ≤ (3151906961059/25000000000000 : ℝ)^845 := by
    have hnat : (2040564913 : ℕ)^1101*25000000000000^845 ≤ 3151906961059^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040564913 10000000000 3151906961059 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534700261/1000000000 : ℝ), (1311812287/2500000000 : ℝ), (-2040564913/10000000000 : ℝ)] ![(44232257765071/100000000000000 : ℝ), (21580057189159/50000000000000 : ℝ), (3151906961059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534700261/1000000000 : ℝ)|^1101 ≤ (44232257765071/100000000000000 : ℝ)^845
        have hw : |(534700261/1000000000 : ℝ)|=(534700261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311812287/2500000000 : ℝ)|^1101 ≤ (21580057189159/50000000000000 : ℝ)^845
        have hw : |(1311812287/2500000000 : ℝ)|=(1311812287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2040564913/10000000000 : ℝ)|^1101 ≤ (3151906961059/25000000000000 : ℝ)^845
        have hw : |(-2040564913/10000000000 : ℝ)|=(2040564913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s7_3 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2150318579/5000000000 : ℝ)*x 0 + (165183193/400000000 : ℝ)*x 1 + (2239001807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150318579/5000000000 : ℝ)^1101 ≤ (16652461018557/50000000000000 : ℝ)^845 := by
    have hnat : (2150318579 : ℕ)^1101*50000000000000^845 ≤ 16652461018557^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150318579 5000000000 16652461018557 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165183193/400000000 : ℝ)^1101 ≤ (1579469544693/5000000000000 : ℝ)^845 := by
    have hnat : (165183193 : ℕ)^1101*5000000000000^845 ≤ 1579469544693^845*400000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165183193 400000000 1579469544693 5000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239001807/5000000000 : ℝ)^1101 ≤ (35105687059703/100000000000000 : ℝ)^845 := by
    have hnat : (2239001807 : ℕ)^1101*100000000000000^845 ≤ 35105687059703^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239001807 5000000000 35105687059703 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150318579/5000000000 : ℝ), (165183193/400000000 : ℝ), (2239001807/5000000000 : ℝ)] ![(16652461018557/50000000000000 : ℝ), (1579469544693/5000000000000 : ℝ), (35105687059703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150318579/5000000000 : ℝ)|^1101 ≤ (16652461018557/50000000000000 : ℝ)^845
        have hw : |(2150318579/5000000000 : ℝ)|=(2150318579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165183193/400000000 : ℝ)|^1101 ≤ (1579469544693/5000000000000 : ℝ)^845
        have hw : |(165183193/400000000 : ℝ)|=(165183193/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239001807/5000000000 : ℝ)|^1101 ≤ (35105687059703/100000000000000 : ℝ)^845
        have hw : |(2239001807/5000000000 : ℝ)|=(2239001807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s7_4 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-489759287/2500000000 : ℝ)*x 0 + (209913093/400000000 : ℝ)*x 1 + (5406846449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489759287/2500000000 : ℝ)^1101 ≤ (2988828068501/25000000000000 : ℝ)^845 := by
    have hnat : (489759287 : ℕ)^1101*25000000000000^845 ≤ 2988828068501^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489759287 2500000000 2988828068501 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209913093/400000000 : ℝ)^1101 ≤ (43166310922793/100000000000000 : ℝ)^845 := by
    have hnat : (209913093 : ℕ)^1101*100000000000000^845 ≤ 43166310922793^845*400000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209913093 400000000 43166310922793 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406846449/10000000000 : ℝ)^1101 ≤ (2804898549273/6250000000000 : ℝ)^845 := by
    have hnat : (5406846449 : ℕ)^1101*6250000000000^845 ≤ 2804898549273^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406846449 10000000000 2804898549273 6250000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489759287/2500000000 : ℝ), (209913093/400000000 : ℝ), (5406846449/10000000000 : ℝ)] ![(2988828068501/25000000000000 : ℝ), (43166310922793/100000000000000 : ℝ), (2804898549273/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489759287/2500000000 : ℝ)|^1101 ≤ (2988828068501/25000000000000 : ℝ)^845
        have hw : |(-489759287/2500000000 : ℝ)|=(489759287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209913093/400000000 : ℝ)|^1101 ≤ (43166310922793/100000000000000 : ℝ)^845
        have hw : |(209913093/400000000 : ℝ)|=(209913093/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406846449/10000000000 : ℝ)|^1101 ≤ (2804898549273/6250000000000 : ℝ)^845
        have hw : |(5406846449/10000000000 : ℝ)|=(5406846449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s7_5 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652650043/5000000000 : ℝ)*x 0 + (-940483789/5000000000 : ℝ)*x 1 + (2703423229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652650043/5000000000 : ℝ)^1101 ≤ (43783298084681/100000000000000 : ℝ)^845 := by
    have hnat : (2652650043 : ℕ)^1101*100000000000000^845 ≤ 43783298084681^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652650043 5000000000 43783298084681 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940483789/5000000000 : ℝ)^1101 ≤ (11338325010821/100000000000000 : ℝ)^845 := by
    have hnat : (940483789 : ℕ)^1101*100000000000000^845 ≤ 11338325010821^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940483789 5000000000 11338325010821 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703423229/5000000000 : ℝ)^1101 ≤ (44878376885703/100000000000000 : ℝ)^845 := by
    have hnat : (2703423229 : ℕ)^1101*100000000000000^845 ≤ 44878376885703^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703423229 5000000000 44878376885703 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652650043/5000000000 : ℝ), (-940483789/5000000000 : ℝ), (2703423229/5000000000 : ℝ)] ![(43783298084681/100000000000000 : ℝ), (11338325010821/100000000000000 : ℝ), (44878376885703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652650043/5000000000 : ℝ)|^1101 ≤ (43783298084681/100000000000000 : ℝ)^845
        have hw : |(2652650043/5000000000 : ℝ)|=(2652650043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-940483789/5000000000 : ℝ)|^1101 ≤ (11338325010821/100000000000000 : ℝ)^845
        have hw : |(-940483789/5000000000 : ℝ)|=(940483789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703423229/5000000000 : ℝ)|^1101 ≤ (44878376885703/100000000000000 : ℝ)^845
        have hw : |(2703423229/5000000000 : ℝ)|=(2703423229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s7_6 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061060011/2000000000 : ℝ)*x 0 + (1081369281/2000000000 : ℝ)*x 1 + (-940483847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061060011/2000000000 : ℝ)^1101 ≤ (43783297751339/100000000000000 : ℝ)^845 := by
    have hnat : (1061060011 : ℕ)^1101*100000000000000^845 ≤ 43783297751339^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061060011 2000000000 43783297751339 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081369281/2000000000 : ℝ)^1101 ≤ (44878376312511/100000000000000 : ℝ)^845 := by
    have hnat : (1081369281 : ℕ)^1101*100000000000000^845 ≤ 44878376312511^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081369281 2000000000 44878376312511 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (940483847/5000000000 : ℝ)^1101 ≤ (113383259219/1000000000000 : ℝ)^845 := by
    have hnat : (940483847 : ℕ)^1101*1000000000000^845 ≤ 113383259219^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940483847 5000000000 113383259219 1000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061060011/2000000000 : ℝ), (1081369281/2000000000 : ℝ), (-940483847/5000000000 : ℝ)] ![(43783297751339/100000000000000 : ℝ), (44878376312511/100000000000000 : ℝ), (113383259219/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061060011/2000000000 : ℝ)|^1101 ≤ (43783297751339/100000000000000 : ℝ)^845
        have hw : |(1061060011/2000000000 : ℝ)|=(1061060011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081369281/2000000000 : ℝ)|^1101 ≤ (44878376312511/100000000000000 : ℝ)^845
        have hw : |(1081369281/2000000000 : ℝ)|=(1081369281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-940483847/5000000000 : ℝ)|^1101 ≤ (113383259219/1000000000000 : ℝ)^845
        have hw : |(-940483847/5000000000 : ℝ)|=(940483847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s7_7 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1075165597/2500000000 : ℝ)*x 0 + (2238372941/5000000000 : ℝ)*x 1 + (1032710787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075165597/2500000000 : ℝ)^1101 ≤ (33305176616869/100000000000000 : ℝ)^845 := by
    have hnat : (1075165597 : ℕ)^1101*100000000000000^845 ≤ 33305176616869^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075165597 2500000000 33305176616869 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238372941/5000000000 : ℝ)^1101 ≤ (17546420154759/50000000000000 : ℝ)^845 := by
    have hnat : (2238372941 : ℕ)^1101*50000000000000^845 ≤ 17546420154759^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238372941 5000000000 17546420154759 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032710787/2500000000 : ℝ)^1101 ≤ (31601983062259/100000000000000 : ℝ)^845 := by
    have hnat : (1032710787 : ℕ)^1101*100000000000000^845 ≤ 31601983062259^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032710787 2500000000 31601983062259 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075165597/2500000000 : ℝ), (2238372941/5000000000 : ℝ), (1032710787/2500000000 : ℝ)] ![(33305176616869/100000000000000 : ℝ), (17546420154759/50000000000000 : ℝ), (31601983062259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075165597/2500000000 : ℝ)|^1101 ≤ (33305176616869/100000000000000 : ℝ)^845
        have hw : |(1075165597/2500000000 : ℝ)|=(1075165597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238372941/5000000000 : ℝ)|^1101 ≤ (17546420154759/50000000000000 : ℝ)^845
        have hw : |(2238372941/5000000000 : ℝ)|=(2238372941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032710787/2500000000 : ℝ)|^1101 ≤ (31601983062259/100000000000000 : ℝ)^845
        have hw : |(1032710787/2500000000 : ℝ)|=(1032710787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s7_8 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-25623191/10000000000 : ℝ)*x 0 + (5872503419/10000000000 : ℝ)*x 1 + (2936263397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25623191/10000000000 : ℝ)^1101 ≤ (262685699/625000000000 : ℝ)^845 := by
    have hnat : (25623191 : ℕ)^1101*625000000000^845 ≤ 262685699^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25623191 10000000000 262685699 625000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5872503419/10000000000 : ℝ)^1101 ≤ (49978855533567/100000000000000 : ℝ)^845 := by
    have hnat : (5872503419 : ℕ)^1101*100000000000000^845 ≤ 49978855533567^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5872503419 10000000000 49978855533567 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2936263397/5000000000 : ℝ)^1101 ≤ (49979114739847/100000000000000 : ℝ)^845 := by
    have hnat : (2936263397 : ℕ)^1101*100000000000000^845 ≤ 49979114739847^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2936263397 5000000000 49979114739847 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25623191/10000000000 : ℝ), (5872503419/10000000000 : ℝ), (2936263397/5000000000 : ℝ)] ![(262685699/625000000000 : ℝ), (49978855533567/100000000000000 : ℝ), (49979114739847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25623191/10000000000 : ℝ)|^1101 ≤ (262685699/625000000000 : ℝ)^845
        have hw : |(-25623191/10000000000 : ℝ)|=(25623191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5872503419/10000000000 : ℝ)|^1101 ≤ (49978855533567/100000000000000 : ℝ)^845
        have hw : |(5872503419/10000000000 : ℝ)|=(5872503419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2936263397/5000000000 : ℝ)|^1101 ≤ (49979114739847/100000000000000 : ℝ)^845
        have hw : |(2936263397/5000000000 : ℝ)|=(2936263397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_s7_9 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1429586999/10000000000 : ℝ)*x 0 + (5512889353/10000000000 : ℝ)*x 1 + (5514061113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1429586999/10000000000 : ℝ)^1101 ≤ (1586004391967/20000000000000 : ℝ)^845 := by
    have hnat : (1429586999 : ℕ)^1101*20000000000000^845 ≤ 1586004391967^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429586999 10000000000 1586004391967 20000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512889353/10000000000 : ℝ)^1101 ≤ (46028615166411/100000000000000 : ℝ)^845 := by
    have hnat : (5512889353 : ℕ)^1101*100000000000000^845 ≤ 46028615166411^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512889353 10000000000 46028615166411 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5514061113/10000000000 : ℝ)^1101 ≤ (2302068143407/5000000000000 : ℝ)^845 := by
    have hnat : (5514061113 : ℕ)^1101*5000000000000^845 ≤ 2302068143407^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514061113 10000000000 2302068143407 5000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1429586999/10000000000 : ℝ), (5512889353/10000000000 : ℝ), (5514061113/10000000000 : ℝ)] ![(1586004391967/20000000000000 : ℝ), (46028615166411/100000000000000 : ℝ), (2302068143407/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1429586999/10000000000 : ℝ)|^1101 ≤ (1586004391967/20000000000000 : ℝ)^845
        have hw : |(1429586999/10000000000 : ℝ)|=(1429586999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512889353/10000000000 : ℝ)|^1101 ≤ (46028615166411/100000000000000 : ℝ)^845
        have hw : |(5512889353/10000000000 : ℝ)|=(5512889353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5514061113/10000000000 : ℝ)|^1101 ≤ (2302068143407/5000000000000 : ℝ)^845
        have hw : |(5514061113/10000000000 : ℝ)|=(5514061113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1444_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3691/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1137/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1137/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1137/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1137/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1137/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1137/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1137/10000 : ℝ) ^ (4403/1024 : ℝ) ≤ (4354360927070159/50000000000000000000 : ℝ) := by
    have hpowers : (1137/10000 : ℝ)^4403 ≤ (4354360927070159/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1137 : ℕ)^4403*50000000000000000000^1024 ≤ 4354360927070159^1024*10000^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1137 10000 4354360927070159 50000000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1137/10000 : ℝ)) (X := (4354360927070159/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2953/20000 : ℝ) ^ (4403/1024 : ℝ) ≤ (13391712096817493/50000000000000000000 : ℝ) := by
    have hpowers : (2953/20000 : ℝ)^4403 ≤ (13391712096817493/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2953 : ℕ)^4403*50000000000000000000^1024 ≤ 13391712096817493^1024*20000^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2953 20000 13391712096817493 50000000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2953/20000 : ℝ)) (X := (13391712096817493/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004354360927070159/25000000000000000000 : ℝ) ≤ (2000081009631951/2000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (25004354360927070159/25000000000000000000 : ℝ)^1024 ≤ (2000081009631951/2000000000000000 : ℝ)^4403 := by
      have hnat : (25004354360927070159 : ℕ)^1024*2000000000000000^4403 ≤ 2000081009631951^4403*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004354360927070159 25000000000000000000 2000081009631951 2000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000081009631951/2000000000000000 : ℝ)) (X := (25004354360927070159/25000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504436518255971913/12500000000000000000 : ℝ) ≤ (10000825323846091/10000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (12504436518255971913/12500000000000000000 : ℝ)^1024 ≤ (10000825323846091/10000000000000000 : ℝ)^4403 := by
      have hnat : (12504436518255971913 : ℕ)^1024*10000000000000000^4403 ≤ 10000825323846091^4403*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504436518255971913 12500000000000000000 10000825323846091 10000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000825323846091/10000000000000000 : ℝ)) (X := (12504436518255971913/12500000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013391712096817493/25000000000000000000 : ℝ) ≤ (10001245599532427/10000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (25013391712096817493/25000000000000000000 : ℝ)^1024 ≤ (10001245599532427/10000000000000000 : ℝ)^4403 := by
      have hnat : (25013391712096817493 : ℕ)^1024*10000000000000000^4403 ≤ 10001245599532427^4403*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013391712096817493 25000000000000000000 10001245599532427 10000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001245599532427/10000000000000000 : ℝ)) (X := (25013391712096817493/25000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4354360927070159/50000000000000000000 : ℝ) ≤ ((6788363613879017517/6790000000000000000 : ℝ)+2*(6566807599/5304687500000 : ℝ)*(1137/10000 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (6788363613879017517/6790000000000000000 : ℝ)+2*(6566807599/5304687500000 : ℝ)*(1137/10000 : ℝ)=(2000081009631951/2000000000000000 : ℝ) by norm_num, show 1+2*(4354360927070159/50000000000000000000 : ℝ)=(25004354360927070159/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13391712096817493/50000000000000000000 : ℝ)+(4354360927070159/50000000000000000000 : ℝ) ≤ ((6788363613879017517/6790000000000000000 : ℝ)+(6566807599/5304687500000 : ℝ)*((2953/20000 : ℝ)+(1137/10000 : ℝ)))^(4403/1024 : ℝ) := by
    rw [show (6788363613879017517/6790000000000000000 : ℝ)+(6566807599/5304687500000 : ℝ)*((2953/20000 : ℝ)+(1137/10000 : ℝ))=(10000825323846091/10000000000000000 : ℝ) by norm_num, show 1+(13391712096817493/50000000000000000000 : ℝ)+(4354360927070159/50000000000000000000 : ℝ)=(12504436518255971913/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13391712096817493/50000000000000000000 : ℝ) ≤ ((6788363613879017517/6790000000000000000 : ℝ)+2*(6566807599/5304687500000 : ℝ)*(2953/20000 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (6788363613879017517/6790000000000000000 : ℝ)+2*(6566807599/5304687500000 : ℝ)*(2953/20000 : ℝ)=(10001245599532427/10000000000000000 : ℝ) by norm_num, show 1+2*(13391712096817493/50000000000000000000 : ℝ)=(25013391712096817493/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6788363613879017517/6790000000000000000 : ℝ)*(X 1 0+X 2 0)+(6566807599/5304687500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (6788363613879017517/6790000000000000000 : ℝ)) (alpha := (6566807599/5304687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6788363613879017517/6790000000000000000 : ℝ)*(X 0 1+X 2 1)+(6566807599/5304687500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (6788363613879017517/6790000000000000000 : ℝ)) (alpha := (6566807599/5304687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6788363613879017517/6790000000000000000 : ℝ)*(X 0 2+X 1 2)+(6566807599/5304687500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (6788363613879017517/6790000000000000000 : ℝ)) (alpha := (6566807599/5304687500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1959027147/10000000000 : ℝ)*X 0 0+(5407427643/10000000000 : ℝ)*X 0 1+(5247248251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673501699/5000000000 : ℝ)*X 1 0+(-2040565741/10000000000 : ℝ)*X 1 1+(2623623867/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534700261/1000000000 : ℝ)*X 2 0+(1311812287/2500000000 : ℝ)*X 2 1+(-2040564913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150318579/5000000000 : ℝ)*X 0 0+(165183193/400000000 : ℝ)*X 0 1+(2239001807/5000000000 : ℝ)*X 0 2+(2150318579/5000000000 : ℝ)*X 1 0+(165183193/400000000 : ℝ)*X 1 1+(2239001807/5000000000 : ℝ)*X 1 2+(2150318579/5000000000 : ℝ)*X 2 0+(165183193/400000000 : ℝ)*X 2 1+(2239001807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-489759287/2500000000 : ℝ)*X 0 0+(209913093/400000000 : ℝ)*X 0 1+(5406846449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652650043/5000000000 : ℝ)*X 1 0+(-940483789/5000000000 : ℝ)*X 1 1+(2703423229/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061060011/2000000000 : ℝ)*X 2 0+(1081369281/2000000000 : ℝ)*X 2 1+(-940483847/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075165597/2500000000 : ℝ)*X 0 0+(2238372941/5000000000 : ℝ)*X 0 1+(1032710787/2500000000 : ℝ)*X 0 2+(1075165597/2500000000 : ℝ)*X 1 0+(2238372941/5000000000 : ℝ)*X 1 1+(1032710787/2500000000 : ℝ)*X 1 2+(1075165597/2500000000 : ℝ)*X 2 0+(2238372941/5000000000 : ℝ)*X 2 1+(1032710787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-25623191/10000000000 : ℝ)*X 0 0+(5872503419/10000000000 : ℝ)*X 0 1+(2936263397/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1429586999/10000000000 : ℝ)*X 0 0+(5512889353/10000000000 : ℝ)*X 0 1+(5514061113/10000000000 : ℝ)*X 0 2+(1429586999/10000000000 : ℝ)*X 1 0+(5512889353/10000000000 : ℝ)*X 1 1+(5514061113/10000000000 : ℝ)*X 1 2+(1429586999/10000000000 : ℝ)*X 2 0+(5512889353/10000000000 : ℝ)*X 2 1+(5514061113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_s7_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9619850278392460216617783/2121875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (141723969/100000000000000 : ℝ)*(lower2) + (19974523/5000000000000 : ℝ)*(lower4) + (238109753/50000000000000 : ℝ)*(lower5) + (56956973213633/1250000000000 : ℝ)*(major0) + (56956973213633/1250000000000 : ℝ)*(major1) + (56956973213633/1250000000000 : ℝ)*(major2) + (49944288016353/800000000000 : ℝ)*(sp0) + (312149704587227/5000000000000 : ℝ)*(sp1) + (1560762561741307/25000000000000 : ℝ)*(sp2) + (57401306248069/2000000000000 : ℝ)*(sp3) + (1703099003/25000000000000 : ℝ)*(sp4) + (3509701293/6250000000000 : ℝ)*(sp5) + (743252509/10000000000000 : ℝ)*(sp8) + (3690747/100000000000000 : ℝ)*(sp9) + (2870065316094197/100000000000000 : ℝ)*(f.failure) + (1560762561741307/25000000000000 : ℝ)*(f.sum) + (5626741859567/848750000000000000000000000 : ℝ)*base65 + (66707500670455739/8487500000000000000000000000000 : ℝ)*base68 + (62743704974144261/8487500000000000000000000000000 : ℝ)*base69 + (2886156191518239/8487500000000000000000000000000 : ℝ)*base72 + (9331858108893/3395000000000000000000000000 : ℝ)*base73 + (10636650358843239/8487500000000000000000000000000 : ℝ)*base76 + (38295318636118239/8487500000000000000000000000000 : ℝ)*base78 + (6064039524968239/8487500000000000000000000000000 : ℝ)*base80 + (1661794938057/3395000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (58095393/10000000000000000000000 : ℝ)*base89 + (58095393/10000000000000000000000 : ℝ)*base91 + (58095393/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (299368492015062366111955977/42437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5575041/20000000000000 : ℝ)*(lower1) + (40890751/20000000000000 : ℝ)*(lower3) + (46579453/100000000000000 : ℝ)*(lower4) + (48218489/50000000000000 : ℝ)*(lower5) + (1147442352029627/25000000000000 : ℝ)*(major0) + (1147442352029627/25000000000000 : ℝ)*(major1) + (1147442352029627/25000000000000 : ℝ)*(major2) + (6494672303/100000000000000 : ℝ)*(sp1) + (628855242673967/10000000000000 : ℝ)*(sp4) + (1572136904894783/25000000000000 : ℝ)*(sp5) + (1257710822850287/20000000000000 : ℝ)*(sp6) + (2890983075536907/100000000000000 : ℝ)*(sp7) + (421877941/25000000000000 : ℝ)*(sp8) + (695652021/50000000000000 : ℝ)*(sp9) + (722746116710237/25000000000000 : ℝ)*(f.failure) + (1257710822850287/20000000000000 : ℝ)*(f.sum) + (28028523985719/8487500000000000000000000000 : ℝ)*base65 + (1419034834134083841/169750000000000000000000000000000 : ℝ)*base68 + (1216506592016416159/169750000000000000000000000000000 : ℝ)*base69 + (918587925525583841/169750000000000000000000000000000 : ℝ)*base72 + (110087553079213/16975000000000000000000000000 : ℝ)*base73 + (2115191835670583841/169750000000000000000000000000000 : ℝ)*base76 + (2118455272460833841/169750000000000000000000000000000 : ℝ)*base78 + (2440189267336833841/169750000000000000000000000000000 : ℝ)*base80 + (21717867942497/4243750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (26541847/2500000000000000000000 : ℝ)*base90 + (26541847/2500000000000000000000 : ℝ)*base92 + (26541847/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1444_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1444_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1444_box_0 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-899722171/5000000000 : ℝ)*x 0 + (5385611769/10000000000 : ℝ)*x 1 + (5385611629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899722171/5000000000 : ℝ)^1101 ≤ (10702277586593/100000000000000 : ℝ)^845 := by
    have hnat : (899722171 : ℕ)^1101*100000000000000^845 ≤ 10702277586593^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899722171 5000000000 10702277586593 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385611769/10000000000 : ℝ)^1101 ≤ (5581107744723/12500000000000 : ℝ)^845 := by
    have hnat : (5385611769 : ℕ)^1101*12500000000000^845 ≤ 5581107744723^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385611769 10000000000 5581107744723 12500000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385611629/10000000000 : ℝ)^1101 ≤ (22324430222749/50000000000000 : ℝ)^845 := by
    have hnat : (5385611629 : ℕ)^1101*50000000000000^845 ≤ 22324430222749^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385611629 10000000000 22324430222749 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-899722171/5000000000 : ℝ), (5385611769/10000000000 : ℝ), (5385611629/10000000000 : ℝ)] ![(10702277586593/100000000000000 : ℝ), (5581107744723/12500000000000 : ℝ), (22324430222749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-899722171/5000000000 : ℝ)|^1101 ≤ (10702277586593/100000000000000 : ℝ)^845
        have hw : |(-899722171/5000000000 : ℝ)|=(899722171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385611769/10000000000 : ℝ)|^1101 ≤ (5581107744723/12500000000000 : ℝ)^845
        have hw : |(5385611769/10000000000 : ℝ)|=(5385611769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385611629/10000000000 : ℝ)|^1101 ≤ (22324430222749/50000000000000 : ℝ)^845
        have hw : |(5385611629/10000000000 : ℝ)|=(5385611629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_1 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5286164551/10000000000 : ℝ)*x 0 + (-1936130679/10000000000 : ℝ)*x 1 + (5385611447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286164551/10000000000 : ℝ)^1101 ≤ (43577646438807/100000000000000 : ℝ)^845 := by
    have hnat : (5286164551 : ℕ)^1101*100000000000000^845 ≤ 43577646438807^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286164551 10000000000 43577646438807 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936130679/10000000000 : ℝ)^1101 ≤ (2943373764747/25000000000000 : ℝ)^845 := by
    have hnat : (1936130679 : ℕ)^1101*25000000000000^845 ≤ 2943373764747^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936130679 10000000000 2943373764747 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385611447/10000000000 : ℝ)^1101 ≤ (22324429239763/50000000000000 : ℝ)^845 := by
    have hnat : (5385611447 : ℕ)^1101*50000000000000^845 ≤ 22324429239763^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385611447 10000000000 22324429239763 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286164551/10000000000 : ℝ), (-1936130679/10000000000 : ℝ), (5385611447/10000000000 : ℝ)] ![(43577646438807/100000000000000 : ℝ), (2943373764747/25000000000000 : ℝ), (22324429239763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286164551/10000000000 : ℝ)|^1101 ≤ (43577646438807/100000000000000 : ℝ)^845
        have hw : |(5286164551/10000000000 : ℝ)|=(5286164551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1936130679/10000000000 : ℝ)|^1101 ≤ (2943373764747/25000000000000 : ℝ)^845
        have hw : |(-1936130679/10000000000 : ℝ)|=(1936130679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385611447/10000000000 : ℝ)|^1101 ≤ (22324429239763/50000000000000 : ℝ)^845
        have hw : |(5385611447/10000000000 : ℝ)|=(5385611447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_2 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (165192639/312500000 : ℝ)*x 0 + (5385611597/10000000000 : ℝ)*x 1 + (-387226123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165192639/312500000 : ℝ)^1101 ≤ (43577645332461/100000000000000 : ℝ)^845 := by
    have hnat : (165192639 : ℕ)^1101*100000000000000^845 ≤ 43577645332461^845*312500000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165192639 312500000 43577645332461 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385611597/10000000000 : ℝ)^1101 ≤ (5581107512479/12500000000000 : ℝ)^845 := by
    have hnat : (5385611597 : ℕ)^1101*12500000000000^845 ≤ 5581107512479^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385611597 10000000000 5581107512479 12500000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387226123/2000000000 : ℝ)^1101 ≤ (5886747275951/50000000000000 : ℝ)^845 := by
    have hnat : (387226123 : ℕ)^1101*50000000000000^845 ≤ 5886747275951^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387226123 2000000000 5886747275951 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165192639/312500000 : ℝ), (5385611597/10000000000 : ℝ), (-387226123/2000000000 : ℝ)] ![(43577645332461/100000000000000 : ℝ), (5581107512479/12500000000000 : ℝ), (5886747275951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165192639/312500000 : ℝ)|^1101 ≤ (43577645332461/100000000000000 : ℝ)^845
        have hw : |(165192639/312500000 : ℝ)|=(165192639/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385611597/10000000000 : ℝ)|^1101 ≤ (5581107512479/12500000000000 : ℝ)^845
        have hw : |(5385611597/10000000000 : ℝ)|=(5385611597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387226123/2000000000 : ℝ)|^1101 ≤ (5886747275951/50000000000000 : ℝ)^845
        have hw : |(-387226123/2000000000 : ℝ)|=(387226123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_3 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4446636667/10000000000 : ℝ)*x 0 + (4231318693/10000000000 : ℝ)*x 1 + (1057829613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4446636667/10000000000 : ℝ)^1101 ≤ (4348203135097/12500000000000 : ℝ)^845 := by
    have hnat : (4446636667 : ℕ)^1101*12500000000000^845 ≤ 4348203135097^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4446636667 10000000000 4348203135097 12500000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231318693/10000000000 : ℝ)^1101 ≤ (8151797164543/25000000000000 : ℝ)^845 := by
    have hnat : (4231318693 : ℕ)^1101*25000000000000^845 ≤ 8151797164543^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231318693 10000000000 8151797164543 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057829613/2500000000 : ℝ)^1101 ≤ (1630359311917/5000000000000 : ℝ)^845 := by
    have hnat : (1057829613 : ℕ)^1101*5000000000000^845 ≤ 1630359311917^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057829613 2500000000 1630359311917 5000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4446636667/10000000000 : ℝ), (4231318693/10000000000 : ℝ), (1057829613/2500000000 : ℝ)] ![(4348203135097/12500000000000 : ℝ), (8151797164543/25000000000000 : ℝ), (1630359311917/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4446636667/10000000000 : ℝ)|^1101 ≤ (4348203135097/12500000000000 : ℝ)^845
        have hw : |(4446636667/10000000000 : ℝ)|=(4446636667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231318693/10000000000 : ℝ)|^1101 ≤ (8151797164543/25000000000000 : ℝ)^845
        have hw : |(4231318693/10000000000 : ℝ)|=(4231318693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057829613/2500000000 : ℝ)|^1101 ≤ (1630359311917/5000000000000 : ℝ)^845
        have hw : |(1057829613/2500000000 : ℝ)|=(1057829613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_4 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121340443/10000000000 : ℝ)*x 0 + (5266739869/10000000000 : ℝ)*x 1 + (1316685037/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121340443/10000000000 : ℝ)^1101 ≤ (1326176128769/10000000000000 : ℝ)^845 := by
    have hnat : (2121340443 : ℕ)^1101*10000000000000^845 ≤ 1326176128769^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121340443 10000000000 1326176128769 10000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266739869/10000000000 : ℝ)^1101 ≤ (43369117849467/100000000000000 : ℝ)^845 := by
    have hnat : (5266739869 : ℕ)^1101*100000000000000^845 ≤ 43369117849467^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266739869 10000000000 43369117849467 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316685037/2500000000 : ℝ)^1101 ≤ (43369120842927/100000000000000 : ℝ)^845 := by
    have hnat : (1316685037 : ℕ)^1101*100000000000000^845 ≤ 43369120842927^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316685037 2500000000 43369120842927 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121340443/10000000000 : ℝ), (5266739869/10000000000 : ℝ), (1316685037/2500000000 : ℝ)] ![(1326176128769/10000000000000 : ℝ), (43369117849467/100000000000000 : ℝ), (43369120842927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121340443/10000000000 : ℝ)|^1101 ≤ (1326176128769/10000000000000 : ℝ)^845
        have hw : |(-2121340443/10000000000 : ℝ)|=(2121340443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266739869/10000000000 : ℝ)|^1101 ≤ (43369117849467/100000000000000 : ℝ)^845
        have hw : |(5266739869/10000000000 : ℝ)|=(5266739869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316685037/2500000000 : ℝ)|^1101 ≤ (43369120842927/100000000000000 : ℝ)^845
        have hw : |(1316685037/2500000000 : ℝ)|=(1316685037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_5 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2684652967/5000000000 : ℝ)*x 0 + (-2480609/12500000 : ℝ)*x 1 + (1053347981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684652967/5000000000 : ℝ)^1101 ≤ (2223640322063/5000000000000 : ℝ)^845 := by
    have hnat : (2684652967 : ℕ)^1101*5000000000000^845 ≤ 2223640322063^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684652967 5000000000 2223640322063 5000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2480609/12500000 : ℝ)^1101 ≤ (12158075306337/100000000000000 : ℝ)^845 := by
    have hnat : (2480609 : ℕ)^1101*100000000000000^845 ≤ 12158075306337^845*12500000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480609 12500000 12158075306337 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053347981/2000000000 : ℝ)^1101 ≤ (1084227955893/2500000000000 : ℝ)^845 := by
    have hnat : (1053347981 : ℕ)^1101*2500000000000^845 ≤ 1084227955893^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053347981 2000000000 1084227955893 2500000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684652967/5000000000 : ℝ), (-2480609/12500000 : ℝ), (1053347981/2000000000 : ℝ)] ![(2223640322063/5000000000000 : ℝ), (12158075306337/100000000000000 : ℝ), (1084227955893/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684652967/5000000000 : ℝ)|^1101 ≤ (2223640322063/5000000000000 : ℝ)^845
        have hw : |(2684652967/5000000000 : ℝ)|=(2684652967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2480609/12500000 : ℝ)|^1101 ≤ (12158075306337/100000000000000 : ℝ)^845
        have hw : |(-2480609/12500000 : ℝ)|=(2480609/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053347981/2000000000 : ℝ)|^1101 ≤ (1084227955893/2500000000000 : ℝ)^845
        have hw : |(1053347981/2000000000 : ℝ)|=(1053347981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_6 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2684652857/5000000000 : ℝ)*x 0 + (5266740267/10000000000 : ℝ)*x 1 + (-1984487011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684652857/5000000000 : ℝ)^1101 ≤ (2779550254187/6250000000000 : ℝ)^845 := by
    have hnat : (2684652857 : ℕ)^1101*6250000000000^845 ≤ 2779550254187^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684652857 5000000000 2779550254187 6250000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266740267/10000000000 : ℝ)^1101 ≤ (10842280529927/25000000000000 : ℝ)^845 := by
    have hnat : (5266740267 : ℕ)^1101*25000000000000^845 ≤ 10842280529927^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266740267 10000000000 10842280529927 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984487011/10000000000 : ℝ)^1101 ≤ (759879612351/6250000000000 : ℝ)^845 := by
    have hnat : (1984487011 : ℕ)^1101*6250000000000^845 ≤ 759879612351^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984487011 10000000000 759879612351 6250000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684652857/5000000000 : ℝ), (5266740267/10000000000 : ℝ), (-1984487011/10000000000 : ℝ)] ![(2779550254187/6250000000000 : ℝ), (10842280529927/25000000000000 : ℝ), (759879612351/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684652857/5000000000 : ℝ)|^1101 ≤ (2779550254187/6250000000000 : ℝ)^845
        have hw : |(2684652857/5000000000 : ℝ)|=(2684652857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266740267/10000000000 : ℝ)|^1101 ≤ (10842280529927/25000000000000 : ℝ)^845
        have hw : |(5266740267/10000000000 : ℝ)|=(5266740267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984487011/10000000000 : ℝ)|^1101 ≤ (759879612351/6250000000000 : ℝ)^845
        have hw : |(-1984487011/10000000000 : ℝ)|=(1984487011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_7 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2076785723/5000000000 : ℝ)*x 0 + (2188900167/5000000000 : ℝ)*x 1 + (4377801107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076785723/5000000000 : ℝ)^1101 ≤ (1273149055441/4000000000000 : ℝ)^845 := by
    have hnat : (2076785723 : ℕ)^1101*4000000000000^845 ≤ 1273149055441^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076785723 5000000000 1273149055441 4000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188900167/5000000000 : ℝ)^1101 ≤ (17042816441351/50000000000000 : ℝ)^845 := by
    have hnat : (2188900167 : ℕ)^1101*50000000000000^845 ≤ 17042816441351^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188900167 5000000000 17042816441351 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4377801107/10000000000 : ℝ)^1101 ≤ (17042820362339/50000000000000 : ℝ)^845 := by
    have hnat : (4377801107 : ℕ)^1101*50000000000000^845 ≤ 17042820362339^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377801107 10000000000 17042820362339 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2076785723/5000000000 : ℝ), (2188900167/5000000000 : ℝ), (4377801107/10000000000 : ℝ)] ![(1273149055441/4000000000000 : ℝ), (17042816441351/50000000000000 : ℝ), (17042820362339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2076785723/5000000000 : ℝ)|^1101 ≤ (1273149055441/4000000000000 : ℝ)^845
        have hw : |(2076785723/5000000000 : ℝ)|=(2076785723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2188900167/5000000000 : ℝ)|^1101 ≤ (17042816441351/50000000000000 : ℝ)^845
        have hw : |(2188900167/5000000000 : ℝ)|=(2188900167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4377801107/10000000000 : ℝ)|^1101 ≤ (17042820362339/50000000000000 : ℝ)^845
        have hw : |(4377801107/10000000000 : ℝ)|=(4377801107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_8 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2053507617/10000000000 : ℝ)*x 0 + (1036890271/2000000000 : ℝ)*x 1 + (2699787753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053507617/10000000000 : ℝ)^1101 ≤ (6355960408539/50000000000000 : ℝ)^845 := by
    have hnat : (2053507617 : ℕ)^1101*50000000000000^845 ≤ 6355960408539^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053507617 10000000000 6355960408539 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036890271/2000000000 : ℝ)^1101 ≤ (531104013733/1250000000000 : ℝ)^845 := by
    have hnat : (1036890271 : ℕ)^1101*1250000000000^845 ≤ 531104013733^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036890271 2000000000 531104013733 1250000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699787753/5000000000 : ℝ)^1101 ≤ (22399879035863/50000000000000 : ℝ)^845 := by
    have hnat : (2699787753 : ℕ)^1101*50000000000000^845 ≤ 22399879035863^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699787753 5000000000 22399879035863 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2053507617/10000000000 : ℝ), (1036890271/2000000000 : ℝ), (2699787753/5000000000 : ℝ)] ![(6355960408539/50000000000000 : ℝ), (531104013733/1250000000000 : ℝ), (22399879035863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2053507617/10000000000 : ℝ)|^1101 ≤ (6355960408539/50000000000000 : ℝ)^845
        have hw : |(-2053507617/10000000000 : ℝ)|=(2053507617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036890271/2000000000 : ℝ)|^1101 ≤ (531104013733/1250000000000 : ℝ)^845
        have hw : |(1036890271/2000000000 : ℝ)|=(1036890271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699787753/5000000000 : ℝ)|^1101 ≤ (22399879035863/50000000000000 : ℝ)^845
        have hw : |(2699787753/5000000000 : ℝ)|=(2699787753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_9 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276393967/10000000000 : ℝ)*x 0 + (-1930324479/10000000000 : ℝ)*x 1 + (5399575679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276393967/10000000000 : ℝ)^1101 ≤ (43472727820889/100000000000000 : ℝ)^845 := by
    have hnat : (5276393967 : ℕ)^1101*100000000000000^845 ≤ 43472727820889^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276393967 10000000000 43472727820889 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930324479/10000000000 : ℝ)^1101 ≤ (11727512210299/100000000000000 : ℝ)^845 := by
    have hnat : (1930324479 : ℕ)^1101*100000000000000^845 ≤ 11727512210299^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930324479 10000000000 11727512210299 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399575679/10000000000 : ℝ)^1101 ≤ (22399879970973/50000000000000 : ℝ)^845 := by
    have hnat : (5399575679 : ℕ)^1101*50000000000000^845 ≤ 22399879970973^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399575679 10000000000 22399879970973 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276393967/10000000000 : ℝ), (-1930324479/10000000000 : ℝ), (5399575679/10000000000 : ℝ)] ![(43472727820889/100000000000000 : ℝ), (11727512210299/100000000000000 : ℝ), (22399879970973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276393967/10000000000 : ℝ)|^1101 ≤ (43472727820889/100000000000000 : ℝ)^845
        have hw : |(5276393967/10000000000 : ℝ)|=(5276393967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1930324479/10000000000 : ℝ)|^1101 ≤ (11727512210299/100000000000000 : ℝ)^845
        have hw : |(-1930324479/10000000000 : ℝ)|=(1930324479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399575679/10000000000 : ℝ)|^1101 ≤ (22399879970973/50000000000000 : ℝ)^845
        have hw : |(5399575679/10000000000 : ℝ)|=(5399575679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_10 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276393337/10000000000 : ℝ)*x 0 + (1349894001/2500000000 : ℝ)*x 1 + (-1930324891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276393337/10000000000 : ℝ)^1101 ≤ (43472721057711/100000000000000 : ℝ)^845 := by
    have hnat : (5276393337 : ℕ)^1101*100000000000000^845 ≤ 43472721057711^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276393337 10000000000 43472721057711 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349894001/2500000000 : ℝ)^1101 ≤ (22399881727683/50000000000000 : ℝ)^845 := by
    have hnat : (1349894001 : ℕ)^1101*50000000000000^845 ≤ 22399881727683^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349894001 2500000000 22399881727683 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1930324891/10000000000 : ℝ)^1101 ≤ (5863757735847/50000000000000 : ℝ)^845 := by
    have hnat : (1930324891 : ℕ)^1101*50000000000000^845 ≤ 5863757735847^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930324891 10000000000 5863757735847 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276393337/10000000000 : ℝ), (1349894001/2500000000 : ℝ), (-1930324891/10000000000 : ℝ)] ![(43472721057711/100000000000000 : ℝ), (22399881727683/50000000000000 : ℝ), (5863757735847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276393337/10000000000 : ℝ)|^1101 ≤ (43472721057711/100000000000000 : ℝ)^845
        have hw : |(5276393337/10000000000 : ℝ)|=(5276393337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349894001/2500000000 : ℝ)|^1101 ≤ (22399881727683/50000000000000 : ℝ)^845
        have hw : |(1349894001/2500000000 : ℝ)|=(1349894001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1930324891/10000000000 : ℝ)|^1101 ≤ (5863757735847/50000000000000 : ℝ)^845
        have hw : |(-1930324891/10000000000 : ℝ)|=(1930324891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_11 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1120127053/2500000000 : ℝ)*x 0 + (2107048061/5000000000 : ℝ)*x 1 + (2107047717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120127053/2500000000 : ℝ)^1101 ≤ (35131272828181/100000000000000 : ℝ)^845 := by
    have hnat : (1120127053 : ℕ)^1101*100000000000000^845 ≤ 35131272828181^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120127053 2500000000 35131272828181 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107048061/5000000000 : ℝ)^1101 ≤ (16217183511823/50000000000000 : ℝ)^845 := by
    have hnat : (2107048061 : ℕ)^1101*50000000000000^845 ≤ 16217183511823^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107048061 5000000000 16217183511823 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107047717/5000000000 : ℝ)^1101 ≤ (8108590031027/25000000000000 : ℝ)^845 := by
    have hnat : (2107047717 : ℕ)^1101*25000000000000^845 ≤ 8108590031027^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107047717 5000000000 8108590031027 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120127053/2500000000 : ℝ), (2107048061/5000000000 : ℝ), (2107047717/5000000000 : ℝ)] ![(35131272828181/100000000000000 : ℝ), (16217183511823/50000000000000 : ℝ), (8108590031027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120127053/2500000000 : ℝ)|^1101 ≤ (35131272828181/100000000000000 : ℝ)^845
        have hw : |(1120127053/2500000000 : ℝ)|=(1120127053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2107048061/5000000000 : ℝ)|^1101 ≤ (16217183511823/50000000000000 : ℝ)^845
        have hw : |(2107048061/5000000000 : ℝ)|=(2107048061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2107047717/5000000000 : ℝ)|^1101 ≤ (8108590031027/25000000000000 : ℝ)^845
        have hw : |(2107047717/5000000000 : ℝ)|=(2107047717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_12 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-233429097/1250000000 : ℝ)*x 0 + (341619113/625000000 : ℝ)*x 1 + (2627803521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233429097/1250000000 : ℝ)^1101 ≤ (5616068476461/50000000000000 : ℝ)^845 := by
    have hnat : (233429097 : ℕ)^1101*50000000000000^845 ≤ 5616068476461^845*1250000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233429097 1250000000 5616068476461 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341619113/625000000 : ℝ)^1101 ≤ (4551815379717/10000000000000 : ℝ)^845 := by
    have hnat : (341619113 : ℕ)^1101*10000000000000^845 ≤ 4551815379717^845*625000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341619113 625000000 4551815379717 10000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627803521/5000000000 : ℝ)^1101 ≤ (2162485462013/5000000000000 : ℝ)^845 := by
    have hnat : (2627803521 : ℕ)^1101*5000000000000^845 ≤ 2162485462013^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627803521 5000000000 2162485462013 5000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-233429097/1250000000 : ℝ), (341619113/625000000 : ℝ), (2627803521/5000000000 : ℝ)] ![(5616068476461/50000000000000 : ℝ), (4551815379717/10000000000000 : ℝ), (2162485462013/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-233429097/1250000000 : ℝ)|^1101 ≤ (5616068476461/50000000000000 : ℝ)^845
        have hw : |(-233429097/1250000000 : ℝ)|=(233429097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341619113/625000000 : ℝ)|^1101 ≤ (4551815379717/10000000000000 : ℝ)^845
        have hw : |(341619113/625000000 : ℝ)|=(341619113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627803521/5000000000 : ℝ)|^1101 ≤ (2162485462013/5000000000000 : ℝ)^845
        have hw : |(2627803521/5000000000 : ℝ)|=(2627803521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_13 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5377091077/10000000000 : ℝ)*x 0 + (-497229167/2500000000 : ℝ)*x 1 + (2627803589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377091077/10000000000 : ℝ)^1101 ≤ (11139210782621/25000000000000 : ℝ)^845 := by
    have hnat : (5377091077 : ℕ)^1101*25000000000000^845 ≤ 11139210782621^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377091077 10000000000 11139210782621 25000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497229167/2500000000 : ℝ)^1101 ≤ (609672307601/5000000000000 : ℝ)^845 := by
    have hnat : (497229167 : ℕ)^1101*5000000000000^845 ≤ 609672307601^845*2500000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497229167 2500000000 609672307601 5000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627803589/5000000000 : ℝ)^1101 ≤ (43249710698503/100000000000000 : ℝ)^845 := by
    have hnat : (2627803589 : ℕ)^1101*100000000000000^845 ≤ 43249710698503^845*5000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627803589 5000000000 43249710698503 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377091077/10000000000 : ℝ), (-497229167/2500000000 : ℝ), (2627803589/5000000000 : ℝ)] ![(11139210782621/25000000000000 : ℝ), (609672307601/5000000000000 : ℝ), (43249710698503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377091077/10000000000 : ℝ)|^1101 ≤ (11139210782621/25000000000000 : ℝ)^845
        have hw : |(5377091077/10000000000 : ℝ)|=(5377091077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-497229167/2500000000 : ℝ)|^1101 ≤ (609672307601/5000000000000 : ℝ)^845
        have hw : |(-497229167/2500000000 : ℝ)|=(497229167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627803589/5000000000 : ℝ)|^1101 ≤ (43249710698503/100000000000000 : ℝ)^845
        have hw : |(2627803589/5000000000 : ℝ)|=(2627803589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_14 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5377091033/10000000000 : ℝ)*x 0 + (525560721/1000000000 : ℝ)*x 1 + (-397783337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377091033/10000000000 : ℝ)^1101 ≤ (22278421327711/50000000000000 : ℝ)^845 := by
    have hnat : (5377091033 : ℕ)^1101*50000000000000^845 ≤ 22278421327711^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377091033 10000000000 22278421327711 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525560721/1000000000 : ℝ)^1101 ≤ (43249711041619/100000000000000 : ℝ)^845 := by
    have hnat : (525560721 : ℕ)^1101*100000000000000^845 ≤ 43249711041619^845*1000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525560721 1000000000 43249711041619 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397783337/2000000000 : ℝ)^1101 ≤ (12193446287817/100000000000000 : ℝ)^845 := by
    have hnat : (397783337 : ℕ)^1101*100000000000000^845 ≤ 12193446287817^845*2000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397783337 2000000000 12193446287817 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377091033/10000000000 : ℝ), (525560721/1000000000 : ℝ), (-397783337/2000000000 : ℝ)] ![(22278421327711/50000000000000 : ℝ), (43249711041619/100000000000000 : ℝ), (12193446287817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377091033/10000000000 : ℝ)|^1101 ≤ (22278421327711/50000000000000 : ℝ)^845
        have hw : |(5377091033/10000000000 : ℝ)|=(5377091033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525560721/1000000000 : ℝ)|^1101 ≤ (43249711041619/100000000000000 : ℝ)^845
        have hw : |(525560721/1000000000 : ℝ)|=(525560721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397783337/2000000000 : ℝ)|^1101 ≤ (12193446287817/100000000000000 : ℝ)^845
        have hw : |(-397783337/2000000000 : ℝ)|=(397783337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1444_box_15 (p : ℝ) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ)) (x : Fin 3 → ℝ) :
    (165026957/400000000 : ℝ)*x 0 + (68617323/156250000 : ℝ)*x 1 + (4391508459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165026957/400000000 : ℝ)^1101 ≤ (15775233114803/50000000000000 : ℝ)^845 := by
    have hnat : (165026957 : ℕ)^1101*50000000000000^845 ≤ 15775233114803^845*400000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165026957 400000000 15775233114803 50000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68617323/156250000 : ℝ)^1101 ≤ (34224767957993/100000000000000 : ℝ)^845 := by
    have hnat : (68617323 : ℕ)^1101*100000000000000^845 ≤ 34224767957993^845*156250000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68617323 156250000 34224767957993 100000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4391508459/10000000000 : ℝ)^1101 ≤ (3422476579509/10000000000000 : ℝ)^845 := by
    have hnat : (4391508459 : ℕ)^1101*10000000000000^845 ≤ 3422476579509^845*10000000000^1101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391508459 10000000000 3422476579509 10000000000000 1101 845 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1101/256 : ℝ)) 1101 845 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165026957/400000000 : ℝ), (68617323/156250000 : ℝ), (4391508459/10000000000 : ℝ)] ![(15775233114803/50000000000000 : ℝ), (34224767957993/100000000000000 : ℝ), (3422476579509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165026957/400000000 : ℝ)|^1101 ≤ (15775233114803/50000000000000 : ℝ)^845
        have hw : |(165026957/400000000 : ℝ)|=(165026957/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68617323/156250000 : ℝ)|^1101 ≤ (34224767957993/100000000000000 : ℝ)^845
        have hw : |(68617323/156250000 : ℝ)|=(68617323/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4391508459/10000000000 : ℝ)|^1101 ≤ (3422476579509/10000000000000 : ℝ)^845
        have hw : |(4391508459/10000000000 : ℝ)|=(4391508459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1444_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62909/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59143/100000 : ℝ) ∧ (80531/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84741/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11371/100000 : ℝ) ^ (4403/1024 : ℝ) ≤ (4356007859224197/50000000000000000000 : ℝ) := by
    have hpowers : (11371/100000 : ℝ)^4403 ≤ (4356007859224197/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11371 : ℕ)^4403*50000000000000000000^1024 ≤ 4356007859224197^1024*100000^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11371 100000 4356007859224197 50000000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11371/100000 : ℝ)) (X := (4356007859224197/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3691/25000 : ℝ) ^ (4403/1024 : ℝ) ≤ (3346953162836977/12500000000000000000 : ℝ) := by
    have hpowers : (3691/25000 : ℝ)^4403 ≤ (3346953162836977/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3691 : ℕ)^4403*12500000000000000000^1024 ≤ 3346953162836977^1024*25000^4403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3691 25000 3346953162836977 12500000000000000000 4403 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3691/25000 : ℝ)) (X := (3346953162836977/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004356007859224197/25000000000000000000 : ℝ) ≤ (400016208053969/400000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (25004356007859224197/25000000000000000000 : ℝ)^1024 ≤ (400016208053969/400000000000000 : ℝ)^4403 := by
      have hnat : (25004356007859224197 : ℕ)^1024*400000000000000^4403 ≤ 400016208053969^4403*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004356007859224197 25000000000000000000 400016208053969 400000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400016208053969/400000000000000 : ℝ)) (X := (25004356007859224197/25000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003548764102114421/10000000000000000000 : ℝ) ≤ (5000412609550899/5000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (10003548764102114421/10000000000000000000 : ℝ)^1024 ≤ (5000412609550899/5000000000000000 : ℝ)^4403 := by
      have hnat : (10003548764102114421 : ℕ)^1024*5000000000000000^4403 ≤ 5000412609550899^4403*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003548764102114421 10000000000000000000 5000412609550899 5000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000412609550899/5000000000000000 : ℝ)) (X := (10003548764102114421/10000000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253346953162836977/6250000000000000000 : ℝ) ≤ (10001245236854371/10000000000000000 : ℝ) ^ (4403/1024 : ℝ) := by
    have hpowers : (6253346953162836977/6250000000000000000 : ℝ)^1024 ≤ (10001245236854371/10000000000000000 : ℝ)^4403 := by
      have hnat : (6253346953162836977 : ℕ)^1024*10000000000000000^4403 ≤ 10001245236854371^4403*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253346953162836977 6250000000000000000 10001245236854371 10000000000000000 1024 4403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001245236854371/10000000000000000 : ℝ)) (X := (6253346953162836977/6250000000000000000 : ℝ)) (by norm_num) 4403 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4356007859224197/50000000000000000000 : ℝ) ≤ ((33921822804448905259/33930000000000000000 : ℝ)+2*(420017752573/339300000000000 : ℝ)*(11371/100000 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (33921822804448905259/33930000000000000000 : ℝ)+2*(420017752573/339300000000000 : ℝ)*(11371/100000 : ℝ)=(400016208053969/400000000000000 : ℝ) by norm_num, show 1+2*(4356007859224197/50000000000000000000 : ℝ)=(25004356007859224197/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3346953162836977/12500000000000000000 : ℝ)+(4356007859224197/50000000000000000000 : ℝ) ≤ ((33921822804448905259/33930000000000000000 : ℝ)+(420017752573/339300000000000 : ℝ)*((3691/25000 : ℝ)+(11371/100000 : ℝ)))^(4403/1024 : ℝ) := by
    rw [show (33921822804448905259/33930000000000000000 : ℝ)+(420017752573/339300000000000 : ℝ)*((3691/25000 : ℝ)+(11371/100000 : ℝ))=(5000412609550899/5000000000000000 : ℝ) by norm_num, show 1+(3346953162836977/12500000000000000000 : ℝ)+(4356007859224197/50000000000000000000 : ℝ)=(10003548764102114421/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3346953162836977/12500000000000000000 : ℝ) ≤ ((33921822804448905259/33930000000000000000 : ℝ)+2*(420017752573/339300000000000 : ℝ)*(3691/25000 : ℝ))^(4403/1024 : ℝ) := by
    rw [show (33921822804448905259/33930000000000000000 : ℝ)+2*(420017752573/339300000000000 : ℝ)*(3691/25000 : ℝ)=(10001245236854371/10000000000000000 : ℝ) by norm_num, show 1+2*(3346953162836977/12500000000000000000 : ℝ)=(6253346953162836977/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33921822804448905259/33930000000000000000 : ℝ)*(X 1 0+X 2 0)+(420017752573/339300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (33921822804448905259/33930000000000000000 : ℝ)) (alpha := (420017752573/339300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33921822804448905259/33930000000000000000 : ℝ)*(X 0 1+X 2 1)+(420017752573/339300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (33921822804448905259/33930000000000000000 : ℝ)) (alpha := (420017752573/339300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33921822804448905259/33930000000000000000 : ℝ)*(X 0 2+X 1 2)+(420017752573/339300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4403/1024 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (33921822804448905259/33930000000000000000 : ℝ)) (alpha := (420017752573/339300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-899722171/5000000000 : ℝ)*X 0 0+(5385611769/10000000000 : ℝ)*X 0 1+(5385611629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286164551/10000000000 : ℝ)*X 1 0+(-1936130679/10000000000 : ℝ)*X 1 1+(5385611447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((165192639/312500000 : ℝ)*X 2 0+(5385611597/10000000000 : ℝ)*X 2 1+(-387226123/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4446636667/10000000000 : ℝ)*X 0 0+(4231318693/10000000000 : ℝ)*X 0 1+(1057829613/2500000000 : ℝ)*X 0 2+(4446636667/10000000000 : ℝ)*X 1 0+(4231318693/10000000000 : ℝ)*X 1 1+(1057829613/2500000000 : ℝ)*X 1 2+(4446636667/10000000000 : ℝ)*X 2 0+(4231318693/10000000000 : ℝ)*X 2 1+(1057829613/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2121340443/10000000000 : ℝ)*X 0 0+(5266739869/10000000000 : ℝ)*X 0 1+(1316685037/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684652967/5000000000 : ℝ)*X 1 0+(-2480609/12500000 : ℝ)*X 1 1+(1053347981/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2684652857/5000000000 : ℝ)*X 2 0+(5266740267/10000000000 : ℝ)*X 2 1+(-1984487011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2076785723/5000000000 : ℝ)*X 0 0+(2188900167/5000000000 : ℝ)*X 0 1+(4377801107/10000000000 : ℝ)*X 0 2+(2076785723/5000000000 : ℝ)*X 1 0+(2188900167/5000000000 : ℝ)*X 1 1+(4377801107/10000000000 : ℝ)*X 1 2+(2076785723/5000000000 : ℝ)*X 2 0+(2188900167/5000000000 : ℝ)*X 2 1+(4377801107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2053507617/10000000000 : ℝ)*X 0 0+(1036890271/2000000000 : ℝ)*X 0 1+(2699787753/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276393967/10000000000 : ℝ)*X 1 0+(-1930324479/10000000000 : ℝ)*X 1 1+(5399575679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276393337/10000000000 : ℝ)*X 2 0+(1349894001/2500000000 : ℝ)*X 2 1+(-1930324891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1120127053/2500000000 : ℝ)*X 0 0+(2107048061/5000000000 : ℝ)*X 0 1+(2107047717/5000000000 : ℝ)*X 0 2+(1120127053/2500000000 : ℝ)*X 1 0+(2107048061/5000000000 : ℝ)*X 1 1+(2107047717/5000000000 : ℝ)*X 1 2+(1120127053/2500000000 : ℝ)*X 2 0+(2107048061/5000000000 : ℝ)*X 2 1+(2107047717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-233429097/1250000000 : ℝ)*X 0 0+(341619113/625000000 : ℝ)*X 0 1+(2627803521/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5377091077/10000000000 : ℝ)*X 1 0+(-497229167/2500000000 : ℝ)*X 1 1+(2627803589/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5377091033/10000000000 : ℝ)*X 2 0+(525560721/1000000000 : ℝ)*X 2 1+(-397783337/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((165026957/400000000 : ℝ)*X 0 0+(68617323/156250000 : ℝ)*X 0 1+(4391508459/10000000000 : ℝ)*X 0 2+(165026957/400000000 : ℝ)*X 1 0+(68617323/156250000 : ℝ)*X 1 1+(4391508459/10000000000 : ℝ)*X 1 2+(165026957/400000000 : ℝ)*X 2 0+(68617323/156250000 : ℝ)*X 2 1+(4391508459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1444_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62909/100000 : ℝ) ≤ (-118578591975338334598648207113057/188500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7785201/100000000000000 : ℝ)*(upper1) + (77700639/100000000000000 : ℝ)*(lower4) + (226156507/100000000000000 : ℝ)*(upper5) + (3033160082994231/100000000000000 : ℝ)*(major0) + (3033160082994231/100000000000000 : ℝ)*(major1) + (3033160082994231/100000000000000 : ℝ)*(major2) + (3911598809/50000000000000 : ℝ)*(sp1) + (1529166551/25000000000000 : ℝ)*(sp2) + (2009184409/100000000000000 : ℝ)*(sp3) + (104419358359951/2500000000000 : ℝ)*(sp4) + (522095894164537/12500000000000 : ℝ)*(sp5) + (1044192214961927/25000000000000 : ℝ)*(sp6) + (1910511985237141/100000000000000 : ℝ)*(sp7) + (20066121/3125000000000 : ℝ)*(sp12) + (38210279888431/2000000000000 : ℝ)*(f.failure) + (4176774976513913/100000000000000 : ℝ)*(f.sum) + (2707176219569/942500000000000000000000000 : ℝ)*base66 + (1359747192296428981/377000000000000000000000000000000 : ℝ)*base67 + (85447107967571019/377000000000000000000000000000000 : ℝ)*base70 + (5845792282811571019/377000000000000000000000000000000 : ℝ)*base72 + (5939242992121/942500000000000000000000000 : ℝ)*base73 + (3678349315381571019/377000000000000000000000000000000 : ℝ)*base76 + (951073263594428981/377000000000000000000000000000000 : ℝ)*base77 + (1239435759679571019/377000000000000000000000000000000 : ℝ)*base80 + (877401959247/471250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (334861/200000000000000000000 : ℝ)*base90 + (334861/200000000000000000000 : ℝ)*base92 + (334861/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59143/100000 : ℝ) ≤ (167235079166510019527987442145453/282750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10612307/100000000000000 : ℝ)*(upper3) + (126733/400000000000 : ℝ)*(upper4) + (27008589/50000000000000 : ℝ)*(lower5) + (1552636316640967/50000000000000 : ℝ)*(major0) + (1552636316640967/50000000000000 : ℝ)*(major1) + (1552636316640967/50000000000000 : ℝ)*(major2) + (2117446108805893/50000000000000 : ℝ)*(sp0) + (2117414711692647/50000000000000 : ℝ)*(sp1) + (26468078460253/625000000000 : ℝ)*(sp2) + (488983792298927/25000000000000 : ℝ)*(sp3) + (91623883/6250000000000 : ℝ)*(sp6) + (96526821/12500000000000 : ℝ)*(sp7) + (901005411/50000000000000 : ℝ)*(sp8) + (32298118657/50000000000000 : ℝ)*(sp9) + (488983985352569/25000000000000 : ℝ)*(f.failure) + (264680876226413/6250000000000 : ℝ)*(f.sum) + (220294437397/4241250000000000000000000000 : ℝ)*base66 + (3347938593210245453/1696500000000000000000000000000000 : ℝ)*base67 + (439785538923245453/1696500000000000000000000000000000 : ℝ)*base69 + (26647775431403754547/1696500000000000000000000000000000 : ℝ)*base72 + (79893888052261/8482500000000000000000000000 : ℝ)*base73 + (8275747903133754547/1696500000000000000000000000000000 : ℝ)*base76 + (7637707112603754547/1696500000000000000000000000000000 : ℝ)*base78 + (7338860317967754547/1696500000000000000000000000000000 : ℝ)*base80 + (54459070577311/8482500000000000000000000000 : ℝ)*base81 + (12636139/2500000000000000000000 : ℝ)*base90 + (12636139/2500000000000000000000 : ℝ)*base92 + (12636139/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80531/100000 : ℝ) ≤ (5838664049260389989528958075633/7250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13669587/100000000000000 : ℝ)*(upper1) + (71848537/50000000000000 : ℝ)*(upper2) + (55670473/50000000000000 : ℝ)*(upper3) + (303001697/100000000000000 : ℝ)*(lower5) + (1706166285876507/50000000000000 : ℝ)*(major0) + (1706166285876507/50000000000000 : ℝ)*(major1) + (1706166285876507/50000000000000 : ℝ)*(major2) + (12355263461/100000000000000 : ℝ)*(sp0) + (38162717937/25000000000000 : ℝ)*(sp2) + (107439272419/100000000000000 : ℝ)*(sp3) + (929692560827953/20000000000000 : ℝ)*(sp8) + (2324237579701613/50000000000000 : ℝ)*(sp9) + (2324161254265739/50000000000000 : ℝ)*(sp10) + (134327382026249/6250000000000 : ℝ)*(sp11) + (2149345551692403/100000000000000 : ℝ)*(f.failure) + (2324237579701613/50000000000000 : ℝ)*(f.sum) + (10629402601/54375000000000000000000000 : ℝ)*base65 + (292037702253475633/43500000000000000000000000000000 : ℝ)*base68 + (60233945427475633/43500000000000000000000000000000 : ℝ)*base70 + (197972435852524367/43500000000000000000000000000000 : ℝ)*base71 + (1223506874137/435000000000000000000000000 : ℝ)*base74 + (294345151390024367/43500000000000000000000000000000 : ℝ)*base75 + (125221311164524367/43500000000000000000000000000000 : ℝ)*base77 + (5719302542524367/43500000000000000000000000000000 : ℝ)*base79 + (369715045261/54375000000000000000000000 : ℝ)*base81 + (63579993/10000000000000000000000 : ℝ)*base90 + (63579993/10000000000000000000000 : ℝ)*base92 + (63579993/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84741/100000 : ℝ) ≤ (-159731706981970422824199311453151/188500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (799149/3125000000000 : ℝ)*(lower0) + (52428999/100000000000000 : ℝ)*(upper3) + (1172929/10000000000000 : ℝ)*(upper5) + (3449977287271011/100000000000000 : ℝ)*(major0) + (3449977287271011/100000000000000 : ℝ)*(major1) + (3449977287271011/100000000000000 : ℝ)*(major2) + (1185565743/50000000000000 : ℝ)*(sp0) + (26875077471/100000000000000 : ℝ)*(sp5) + (2044143279/12500000000000 : ℝ)*(sp7) + (31491473/4000000000000 : ℝ)*(sp8) + (118878511822223/2500000000000 : ℝ)*(sp12) + (4755116756229761/100000000000000 : ℝ)*(sp13) + (148598238478351/3125000000000 : ℝ)*(sp14) + (2173040692118959/100000000000000 : ℝ)*(sp15) + (217305704526519/10000000000000 : ℝ)*(f.failure) + (148598238478351/3125000000000 : ℝ)*(f.sum) + (6190550747783/1885000000000000000000000000 : ℝ)*base66 + (3820490095659839239/377000000000000000000000000000000 : ℝ)*base68 + (2109071784927839239/377000000000000000000000000000000 : ℝ)*base70 + (4302723294340839239/377000000000000000000000000000000 : ℝ)*base72 + (1912628820987/1885000000000000000000000000 : ℝ)*base73 + (4076661525160839239/377000000000000000000000000000000 : ℝ)*base76 + (4857024564005839239/377000000000000000000000000000000 : ℝ)*base78 + (941921204786839239/377000000000000000000000000000000 : ℝ)*base80 + (4861889546429/942500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4103589/1000000000000000000000 : ℝ)*base90 + (4103589/1000000000000000000000 : ℝ)*base92 + (4103589/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1444_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62909/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59143/100000 : ℝ) else (80531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84741/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1444_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1444_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62909/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59143/100000 : ℝ) else (80531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84741/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1444_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1444_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1444_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4403/1024 : ℝ) ≤ p) (hpb : p ≤ (1101/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158761469/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62909/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59143/100000 : ℝ) else (80531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84741/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1444_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

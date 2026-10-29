-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1622_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:58:21.922684+00:00
-- url     : https://prove2.me/submissions/b232bac3-ff57-43e4-bcc0-56cf79f54ae5

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
theorem support_rectangle_w1622_s3_0 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1674455909/10000000000 : ℝ)*x 0 + (5456186647/10000000000 : ℝ)*x 1 + (1295390459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674455909/10000000000 : ℝ)^4807 ≤ (10322579856341/100000000000000 : ℝ)^3783 := by
    have hnat : (1674455909 : ℕ)^4807*100000000000000^3783 ≤ 10322579856341^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674455909 10000000000 10322579856341 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456186647/10000000000 : ℝ)^4807 ≤ (9261880352807/20000000000000 : ℝ)^3783 := by
    have hnat : (5456186647 : ℕ)^4807*20000000000000^3783 ≤ 9261880352807^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456186647 10000000000 9261880352807 20000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295390459/2500000000 : ℝ)^4807 ≤ (43368018367829/100000000000000 : ℝ)^3783 := by
    have hnat : (1295390459 : ℕ)^4807*100000000000000^3783 ≤ 43368018367829^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295390459 2500000000 43368018367829 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1674455909/10000000000 : ℝ), (5456186647/10000000000 : ℝ), (1295390459/2500000000 : ℝ)] ![(10322579856341/100000000000000 : ℝ), (9261880352807/20000000000000 : ℝ), (43368018367829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1674455909/10000000000 : ℝ)|^4807 ≤ (10322579856341/100000000000000 : ℝ)^3783
        have hw : |(-1674455909/10000000000 : ℝ)|=(1674455909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456186647/10000000000 : ℝ)|^4807 ≤ (9261880352807/20000000000000 : ℝ)^3783
        have hw : |(5456186647/10000000000 : ℝ)|=(5456186647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295390459/2500000000 : ℝ)|^4807 ≤ (43368018367829/100000000000000 : ℝ)^3783
        have hw : |(1295390459/2500000000 : ℝ)|=(1295390459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s3_1 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070390731/2000000000 : ℝ)*x 0 + (-908001/5000000 : ℝ)*x 1 + (5060119/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070390731/2000000000 : ℝ)^4807 ≤ (45188175325641/100000000000000 : ℝ)^3783 := by
    have hnat : (1070390731 : ℕ)^4807*100000000000000^3783 ≤ 45188175325641^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070390731 2000000000 45188175325641 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908001/5000000 : ℝ)^4807 ≤ (11443806072297/100000000000000 : ℝ)^3783 := by
    have hnat : (908001 : ℕ)^4807*100000000000000^3783 ≤ 11443806072297^3783*5000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908001 5000000 11443806072297 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5060119/9765625 : ℝ)^4807 ≤ (43368018580533/100000000000000 : ℝ)^3783 := by
    have hnat : (5060119 : ℕ)^4807*100000000000000^3783 ≤ 43368018580533^3783*9765625^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060119 9765625 43368018580533 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070390731/2000000000 : ℝ), (-908001/5000000 : ℝ), (5060119/9765625 : ℝ)] ![(45188175325641/100000000000000 : ℝ), (11443806072297/100000000000000 : ℝ), (43368018580533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070390731/2000000000 : ℝ)|^4807 ≤ (45188175325641/100000000000000 : ℝ)^3783
        have hw : |(1070390731/2000000000 : ℝ)|=(1070390731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-908001/5000000 : ℝ)|^4807 ≤ (11443806072297/100000000000000 : ℝ)^3783
        have hw : |(-908001/5000000 : ℝ)|=(908001/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5060119/9765625 : ℝ)|^4807 ≤ (43368018580533/100000000000000 : ℝ)^3783
        have hw : |(5060119/9765625 : ℝ)|=(5060119/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s3_2 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675976827/5000000000 : ℝ)*x 0 + (5181561849/10000000000 : ℝ)*x 1 + (-1816002011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675976827/5000000000 : ℝ)^4807 ≤ (1412130478591/3125000000000 : ℝ)^3783 := by
    have hnat : (2675976827 : ℕ)^4807*3125000000000^3783 ≤ 1412130478591^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675976827 5000000000 1412130478591 3125000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181561849/10000000000 : ℝ)^4807 ≤ (43368018506087/100000000000000 : ℝ)^3783 := by
    have hnat : (5181561849 : ℕ)^4807*100000000000000^3783 ≤ 43368018506087^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181561849 10000000000 43368018506087 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1816002011/10000000000 : ℝ)^4807 ≤ (5721903080189/50000000000000 : ℝ)^3783 := by
    have hnat : (1816002011 : ℕ)^4807*50000000000000^3783 ≤ 5721903080189^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816002011 10000000000 5721903080189 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675976827/5000000000 : ℝ), (5181561849/10000000000 : ℝ), (-1816002011/10000000000 : ℝ)] ![(1412130478591/3125000000000 : ℝ), (43368018506087/100000000000000 : ℝ), (5721903080189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675976827/5000000000 : ℝ)|^4807 ≤ (1412130478591/3125000000000 : ℝ)^3783
        have hw : |(2675976827/5000000000 : ℝ)|=(2675976827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181561849/10000000000 : ℝ)|^4807 ≤ (43368018506087/100000000000000 : ℝ)^3783
        have hw : |(5181561849/10000000000 : ℝ)|=(5181561849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1816002011/10000000000 : ℝ)|^4807 ≤ (5721903080189/50000000000000 : ℝ)^3783
        have hw : |(-1816002011/10000000000 : ℝ)|=(1816002011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s3_3 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050676867/2500000000 : ℝ)*x 0 + (3870514597/10000000000 : ℝ)*x 1 + (4556036807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050676867/2500000000 : ℝ)^4807 ≤ (519331079373/1562500000000 : ℝ)^3783 := by
    have hnat : (1050676867 : ℕ)^4807*1562500000000^3783 ≤ 519331079373^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050676867 2500000000 519331079373 1562500000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3870514597/10000000000 : ℝ)^4807 ≤ (29935328650819/100000000000000 : ℝ)^3783 := by
    have hnat : (3870514597 : ℕ)^4807*100000000000000^3783 ≤ 29935328650819^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3870514597 10000000000 29935328650819 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4556036807/10000000000 : ℝ)^4807 ≤ (36827482259529/100000000000000 : ℝ)^3783 := by
    have hnat : (4556036807 : ℕ)^4807*100000000000000^3783 ≤ 36827482259529^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556036807 10000000000 36827482259529 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050676867/2500000000 : ℝ), (3870514597/10000000000 : ℝ), (4556036807/10000000000 : ℝ)] ![(519331079373/1562500000000 : ℝ), (29935328650819/100000000000000 : ℝ), (36827482259529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050676867/2500000000 : ℝ)|^4807 ≤ (519331079373/1562500000000 : ℝ)^3783
        have hw : |(1050676867/2500000000 : ℝ)|=(1050676867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3870514597/10000000000 : ℝ)|^4807 ≤ (29935328650819/100000000000000 : ℝ)^3783
        have hw : |(3870514597/10000000000 : ℝ)|=(3870514597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4556036807/10000000000 : ℝ)|^4807 ≤ (36827482259529/100000000000000 : ℝ)^3783
        have hw : |(4556036807/10000000000 : ℝ)|=(4556036807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s3_4 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1674524957/10000000000 : ℝ)*x 0 + (5183618439/10000000000 : ℝ)*x 1 + (218164329/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674524957/10000000000 : ℝ)^4807 ≤ (10323120742469/100000000000000 : ℝ)^3783 := by
    have hnat : (1674524957 : ℕ)^4807*100000000000000^3783 ≤ 10323120742469^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674524957 10000000000 10323120742469 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183618439/10000000000 : ℝ)^4807 ≤ (10847472994469/25000000000000 : ℝ)^3783 := by
    have hnat : (5183618439 : ℕ)^4807*25000000000000^3783 ≤ 10847472994469^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183618439 10000000000 10847472994469 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218164329/400000000 : ℝ)^4807 ≤ (9257397452649/20000000000000 : ℝ)^3783 := by
    have hnat : (218164329 : ℕ)^4807*20000000000000^3783 ≤ 9257397452649^3783*400000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218164329 400000000 9257397452649 20000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1674524957/10000000000 : ℝ), (5183618439/10000000000 : ℝ), (218164329/400000000 : ℝ)] ![(10323120742469/100000000000000 : ℝ), (10847472994469/25000000000000 : ℝ), (9257397452649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1674524957/10000000000 : ℝ)|^4807 ≤ (10323120742469/100000000000000 : ℝ)^3783
        have hw : |(-1674524957/10000000000 : ℝ)|=(1674524957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183618439/10000000000 : ℝ)|^4807 ≤ (10847472994469/25000000000000 : ℝ)^3783
        have hw : |(5183618439/10000000000 : ℝ)|=(5183618439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218164329/400000000 : ℝ)|^4807 ≤ (9257397452649/20000000000000 : ℝ)^3783
        have hw : |(218164329/400000000 : ℝ)|=(218164329/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s3_5 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278870871/10000000000 : ℝ)*x 0 + (-1543456183/10000000000 : ℝ)*x 1 + (545410739/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278870871/10000000000 : ℝ)^4807 ≤ (888110806831/2000000000000 : ℝ)^3783 := by
    have hnat : (5278870871 : ℕ)^4807*2000000000000^3783 ≤ 888110806831^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278870871 10000000000 888110806831 2000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1543456183/10000000000 : ℝ)^4807 ≤ (1163435173481/12500000000000 : ℝ)^3783 := by
    have hnat : (1543456183 : ℕ)^4807*12500000000000^3783 ≤ 1163435173481^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543456183 10000000000 1163435173481 12500000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545410739/1000000000 : ℝ)^4807 ≤ (46286978258749/100000000000000 : ℝ)^3783 := by
    have hnat : (545410739 : ℕ)^4807*100000000000000^3783 ≤ 46286978258749^3783*1000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545410739 1000000000 46286978258749 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278870871/10000000000 : ℝ), (-1543456183/10000000000 : ℝ), (545410739/1000000000 : ℝ)] ![(888110806831/2000000000000 : ℝ), (1163435173481/12500000000000 : ℝ), (46286978258749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278870871/10000000000 : ℝ)|^4807 ≤ (888110806831/2000000000000 : ℝ)^3783
        have hw : |(5278870871/10000000000 : ℝ)|=(5278870871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1543456183/10000000000 : ℝ)|^4807 ≤ (1163435173481/12500000000000 : ℝ)^3783
        have hw : |(-1543456183/10000000000 : ℝ)|=(1543456183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545410739/1000000000 : ℝ)|^4807 ≤ (46286978258749/100000000000000 : ℝ)^3783
        have hw : |(545410739/1000000000 : ℝ)|=(545410739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s3_6 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278870381/10000000000 : ℝ)*x 0 + (5454107917/10000000000 : ℝ)*x 1 + (-12347649/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278870381/10000000000 : ℝ)^4807 ≤ (44405535103979/100000000000000 : ℝ)^3783 := by
    have hnat : (5278870381 : ℕ)^4807*100000000000000^3783 ≤ 44405535103979^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278870381 10000000000 44405535103979 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454107917/10000000000 : ℝ)^4807 ≤ (23143491970913/50000000000000 : ℝ)^3783 := by
    have hnat : (5454107917 : ℕ)^4807*50000000000000^3783 ≤ 23143491970913^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454107917 10000000000 23143491970913 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12347649/80000000 : ℝ)^4807 ≤ (4653740471709/50000000000000 : ℝ)^3783 := by
    have hnat : (12347649 : ℕ)^4807*50000000000000^3783 ≤ 4653740471709^3783*80000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12347649 80000000 4653740471709 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278870381/10000000000 : ℝ), (5454107917/10000000000 : ℝ), (-12347649/80000000 : ℝ)] ![(44405535103979/100000000000000 : ℝ), (23143491970913/50000000000000 : ℝ), (4653740471709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278870381/10000000000 : ℝ)|^4807 ≤ (44405535103979/100000000000000 : ℝ)^3783
        have hw : |(5278870381/10000000000 : ℝ)|=(5278870381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454107917/10000000000 : ℝ)|^4807 ≤ (23143491970913/50000000000000 : ℝ)^3783
        have hw : |(5454107917/10000000000 : ℝ)|=(5454107917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12347649/80000000 : ℝ)|^4807 ≤ (4653740471709/50000000000000 : ℝ)^3783
        have hw : |(-12347649/80000000 : ℝ)|=(12347649/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s3_7 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4202879289/10000000000 : ℝ)*x 0 + (4550901521/10000000000 : ℝ)*x 1 + (3875704173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202879289/10000000000 : ℝ)^4807 ≤ (33238915758653/100000000000000 : ℝ)^3783 := by
    have hnat : (4202879289 : ℕ)^4807*100000000000000^3783 ≤ 33238915758653^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202879289 10000000000 33238915758653 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4550901521/10000000000 : ℝ)^4807 ≤ (18387372294239/50000000000000 : ℝ)^3783 := by
    have hnat : (4550901521 : ℕ)^4807*50000000000000^3783 ≤ 18387372294239^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4550901521 10000000000 18387372294239 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3875704173/10000000000 : ℝ)^4807 ≤ (29986339641177/100000000000000 : ℝ)^3783 := by
    have hnat : (3875704173 : ℕ)^4807*100000000000000^3783 ≤ 29986339641177^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3875704173 10000000000 29986339641177 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202879289/10000000000 : ℝ), (4550901521/10000000000 : ℝ), (3875704173/10000000000 : ℝ)] ![(33238915758653/100000000000000 : ℝ), (18387372294239/50000000000000 : ℝ), (29986339641177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202879289/10000000000 : ℝ)|^4807 ≤ (33238915758653/100000000000000 : ℝ)^3783
        have hw : |(4202879289/10000000000 : ℝ)|=(4202879289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4550901521/10000000000 : ℝ)|^4807 ≤ (18387372294239/50000000000000 : ℝ)^3783
        have hw : |(4550901521/10000000000 : ℝ)|=(4550901521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3875704173/10000000000 : ℝ)|^4807 ≤ (29986339641177/100000000000000 : ℝ)^3783
        have hw : |(3875704173/10000000000 : ℝ)|=(3875704173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1622_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3289/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/125 : ℝ)*pair X i i ≤ pair X i h) :
    (10503/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1633/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3289/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (13/125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3289/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (13/125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3289/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (13/125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3289/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (13/125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3289/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (13/125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3289/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (13/125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (13/125 : ℝ) ^ (4803/1024 : ℝ) ≤ (2451681177511177/100000000000000000000 : ℝ) := by
    have hpowers : (13/125 : ℝ)^4803 ≤ (2451681177511177/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13 : ℕ)^4803*100000000000000000000^1024 ≤ 2451681177511177^1024*125^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13 125 2451681177511177 100000000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13/125 : ℝ)) (X := (2451681177511177/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3289/20000 : ℝ) ^ (4803/1024 : ℝ) ≤ (2103110184635873/10000000000000000000 : ℝ) := by
    have hpowers : (3289/20000 : ℝ)^4803 ≤ (2103110184635873/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3289 : ℕ)^4803*10000000000000000000^1024 ≤ 2103110184635873^1024*20000^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3289 20000 2103110184635873 10000000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3289/20000 : ℝ)) (X := (2103110184635873/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002451681177511177/50000000000000000000 : ℝ) ≤ (10000104537709751/10000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (50002451681177511177/50000000000000000000 : ℝ)^1024 ≤ (10000104537709751/10000000000000000 : ℝ)^4803 := by
      have hnat : (50002451681177511177 : ℕ)^1024*10000000000000000^4803 ≤ 10000104537709751^4803*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002451681177511177 50000000000000000000 10000104537709751 10000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000104537709751/10000000000000000 : ℝ)) (X := (50002451681177511177/50000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100023482783023869907/100000000000000000000 : ℝ) ≤ (10000500606885139/10000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (100023482783023869907/100000000000000000000 : ℝ)^1024 ≤ (10000500606885139/10000000000000000 : ℝ)^4803 := by
      have hnat : (100023482783023869907 : ℕ)^1024*10000000000000000^4803 ≤ 10000500606885139^4803*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100023482783023869907 100000000000000000000 10000500606885139 10000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000500606885139/10000000000000000 : ℝ)) (X := (100023482783023869907/100000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002103110184635873/5000000000000000000 : ℝ) ≤ (10000896676060527/10000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (5002103110184635873/5000000000000000000 : ℝ)^1024 ≤ (10000896676060527/10000000000000000 : ℝ)^4803 := by
      have hnat : (5002103110184635873 : ℕ)^1024*10000000000000000^4803 ≤ 10000896676060527^4803*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002103110184635873 5000000000000000000 10000896676060527 10000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000896676060527/10000000000000000 : ℝ)) (X := (5002103110184635873/5000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2451681177511177/100000000000000000000 : ℝ) ≤ ((929882979870882683/930000000000000000 : ℝ)+2*(99017293847/151125000000000 : ℝ)*(13/125 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (929882979870882683/930000000000000000 : ℝ)+2*(99017293847/151125000000000 : ℝ)*(13/125 : ℝ)=(10000104537709751/10000000000000000 : ℝ) by norm_num, show 1+2*(2451681177511177/100000000000000000000 : ℝ)=(50002451681177511177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2103110184635873/10000000000000000000 : ℝ)+(2451681177511177/100000000000000000000 : ℝ) ≤ ((929882979870882683/930000000000000000 : ℝ)+(99017293847/151125000000000 : ℝ)*((3289/20000 : ℝ)+(13/125 : ℝ)))^(4803/1024 : ℝ) := by
    rw [show (929882979870882683/930000000000000000 : ℝ)+(99017293847/151125000000000 : ℝ)*((3289/20000 : ℝ)+(13/125 : ℝ))=(10000500606885139/10000000000000000 : ℝ) by norm_num, show 1+(2103110184635873/10000000000000000000 : ℝ)+(2451681177511177/100000000000000000000 : ℝ)=(100023482783023869907/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2103110184635873/10000000000000000000 : ℝ) ≤ ((929882979870882683/930000000000000000 : ℝ)+2*(99017293847/151125000000000 : ℝ)*(3289/20000 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (929882979870882683/930000000000000000 : ℝ)+2*(99017293847/151125000000000 : ℝ)*(3289/20000 : ℝ)=(10000896676060527/10000000000000000 : ℝ) by norm_num, show 1+2*(2103110184635873/10000000000000000000 : ℝ)=(5002103110184635873/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (929882979870882683/930000000000000000 : ℝ)*(X 1 0+X 2 0)+(99017293847/151125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (13/125 : ℝ)) (hi := (3289/20000 : ℝ)) (c := (929882979870882683/930000000000000000 : ℝ)) (alpha := (99017293847/151125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (929882979870882683/930000000000000000 : ℝ)*(X 0 1+X 2 1)+(99017293847/151125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (13/125 : ℝ)) (hi := (3289/20000 : ℝ)) (c := (929882979870882683/930000000000000000 : ℝ)) (alpha := (99017293847/151125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (929882979870882683/930000000000000000 : ℝ)*(X 0 2+X 1 2)+(99017293847/151125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (13/125 : ℝ)) (hi := (3289/20000 : ℝ)) (c := (929882979870882683/930000000000000000 : ℝ)) (alpha := (99017293847/151125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1674455909/10000000000 : ℝ)*X 0 0+(5456186647/10000000000 : ℝ)*X 0 1+(1295390459/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070390731/2000000000 : ℝ)*X 1 0+(-908001/5000000 : ℝ)*X 1 1+(5060119/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675976827/5000000000 : ℝ)*X 2 0+(5181561849/10000000000 : ℝ)*X 2 1+(-1816002011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1050676867/2500000000 : ℝ)*X 0 0+(3870514597/10000000000 : ℝ)*X 0 1+(4556036807/10000000000 : ℝ)*X 0 2+(1050676867/2500000000 : ℝ)*X 1 0+(3870514597/10000000000 : ℝ)*X 1 1+(4556036807/10000000000 : ℝ)*X 1 2+(1050676867/2500000000 : ℝ)*X 2 0+(3870514597/10000000000 : ℝ)*X 2 1+(4556036807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1674524957/10000000000 : ℝ)*X 0 0+(5183618439/10000000000 : ℝ)*X 0 1+(218164329/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278870871/10000000000 : ℝ)*X 1 0+(-1543456183/10000000000 : ℝ)*X 1 1+(545410739/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278870381/10000000000 : ℝ)*X 2 0+(5454107917/10000000000 : ℝ)*X 2 1+(-12347649/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4202879289/10000000000 : ℝ)*X 0 0+(4550901521/10000000000 : ℝ)*X 0 1+(3875704173/10000000000 : ℝ)*X 0 2+(4202879289/10000000000 : ℝ)*X 1 0+(4550901521/10000000000 : ℝ)*X 1 1+(3875704173/10000000000 : ℝ)*X 1 2+(4202879289/10000000000 : ℝ)*X 2 0+(4550901521/10000000000 : ℝ)*X 2 1+(3875704173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2886354092836647888123/387500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1188930587/100000000000000 : ℝ)*(base19) + (276695241/25000000000000 : ℝ)*(base23) + (21800981/50000000000000 : ℝ)*(lower2) + (36942317/20000000000000 : ℝ)*(upper3) + (58532849/50000000000000 : ℝ)*(upper5) + (79689302445649/3125000000000 : ℝ)*(major0) + (79689302445649/3125000000000 : ℝ)*(major1) + (79689302445649/3125000000000 : ℝ)*(major2) + (910336702786247/25000000000000 : ℝ)*(sp0) + (1820680065835257/50000000000000 : ℝ)*(sp1) + (455170026727517/12500000000000 : ℝ)*(sp2) + (729373730944047/50000000000000 : ℝ)*(sp3) + (14509456111/100000000000000 : ℝ)*(sp4) + (6325743809/100000000000000 : ℝ)*(sp7) + (1458753787631903/100000000000000 : ℝ)*(f.failure) + (36413613206011/1000000000000 : ℝ)*(f.sum) + (962344654859/1162500000000000000000000000 : ℝ)*base65 + (1764727405717089/968750000000000000000000000000 : ℝ)*base67 + (4558084913029589/968750000000000000000000000000 : ℝ)*base69 + (6102819644939161/968750000000000000000000000000 : ℝ)*base72 + (10632390600493/2325000000000000000000000000 : ℝ)*base73 + (3518599907939161/968750000000000000000000000000 : ℝ)*base76 + (4063292964623339/968750000000000000000000000000 : ℝ)*base77 + (6080389796439161/968750000000000000000000000000 : ℝ)*base80 + (4112895970093/2325000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (34750853/5000000000000000000000 : ℝ)*base90 + (34750853/5000000000000000000000 : ℝ)*base92 + (34750853/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (471260136842555436662263167/50375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1800095473/100000000000000 : ℝ)*(base19) + (1418797667/100000000000000 : ℝ)*(base23) + (6337813/25000000000000 : ℝ)*(upper2) + (21005643/100000000000000 : ℝ)*(upper3) + (402958371/100000000000000 : ℝ)*(upper5) + (647256176013073/25000000000000 : ℝ)*(major0) + (647256176013073/25000000000000 : ℝ)*(major1) + (647256176013073/25000000000000 : ℝ)*(major2) + (717089083/4000000000000 : ℝ)*(sp1) + (365750883/3125000000000 : ℝ)*(sp2) + (369700432402589/10000000000000 : ℝ)*(sp4) + (1848492298351671/50000000000000 : ℝ)*(sp5) + (3696991201199967/100000000000000 : ℝ)*(sp6) + (740522386122013/50000000000000 : ℝ)*(sp7) + (740522386122013/50000000000000 : ℝ)*(f.failure) + (369700432402589/10000000000000 : ℝ)*(f.sum) + (5573126759597/944531250000000000000000000 : ℝ)*base66 + (377548917111475611/100750000000000000000000000000000 : ℝ)*base68 + (377399453680475611/100750000000000000000000000000000 : ℝ)*base70 + (135642540189774389/100750000000000000000000000000000 : ℝ)*base71 + (14039227643963/3778125000000000000000000000 : ℝ)*base74 + (514398910822024389/100750000000000000000000000000000 : ℝ)*base75 + (458738617843225611/100750000000000000000000000000000 : ℝ)*base78 + (45583548191225611/100750000000000000000000000000000 : ℝ)*base80 + (136614716527279/30225000000000000000000000000 : ℝ)*base82 + (2847537/2500000000000000000000 : ℝ)*base89 + (2847537/2500000000000000000000 : ℝ)*base91 + (2847537/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1622_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3289/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10503/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1622_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1622_s4_0 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1674543799/10000000000 : ℝ)*x 0 + (545574643/1000000000 : ℝ)*x 1 + (323871469/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674543799/10000000000 : ℝ)^4807 ≤ (2580817085487/25000000000000 : ℝ)^3783 := by
    have hnat : (1674543799 : ℕ)^4807*25000000000000^3783 ≤ 2580817085487^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674543799 10000000000 2580817085487 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545574643/1000000000 : ℝ)^4807 ≤ (46304654101949/100000000000000 : ℝ)^3783 := by
    have hnat : (545574643 : ℕ)^4807*100000000000000^3783 ≤ 46304654101949^3783*1000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545574643 1000000000 46304654101949 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323871469/625000000 : ℝ)^4807 ≤ (43372077533269/100000000000000 : ℝ)^3783 := by
    have hnat : (323871469 : ℕ)^4807*100000000000000^3783 ≤ 43372077533269^3783*625000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323871469 625000000 43372077533269 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1674543799/10000000000 : ℝ), (545574643/1000000000 : ℝ), (323871469/625000000 : ℝ)] ![(2580817085487/25000000000000 : ℝ), (46304654101949/100000000000000 : ℝ), (43372077533269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1674543799/10000000000 : ℝ)|^4807 ≤ (2580817085487/25000000000000 : ℝ)^3783
        have hw : |(-1674543799/10000000000 : ℝ)|=(1674543799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545574643/1000000000 : ℝ)|^4807 ≤ (46304654101949/100000000000000 : ℝ)^3783
        have hw : |(545574643/1000000000 : ℝ)|=(545574643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323871469/625000000 : ℝ)|^4807 ≤ (43372077533269/100000000000000 : ℝ)^3783
        have hw : |(323871469/625000000 : ℝ)|=(323871469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s4_1 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351835467/10000000000 : ℝ)*x 0 + (-1815653889/10000000000 : ℝ)*x 1 + (5181943171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351835467/10000000000 : ℝ)^4807 ≤ (22593453658333/50000000000000 : ℝ)^3783 := by
    have hnat : (5351835467 : ℕ)^4807*50000000000000^3783 ≤ 22593453658333^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351835467 10000000000 22593453658333 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1815653889/10000000000 : ℝ)^4807 ≤ (11441018677873/100000000000000 : ℝ)^3783 := by
    have hnat : (1815653889 : ℕ)^4807*100000000000000^3783 ≤ 11441018677873^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815653889 10000000000 11441018677873 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181943171/10000000000 : ℝ)^4807 ≤ (10843018497917/25000000000000 : ℝ)^3783 := by
    have hnat : (5181943171 : ℕ)^4807*25000000000000^3783 ≤ 10843018497917^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181943171 10000000000 10843018497917 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351835467/10000000000 : ℝ), (-1815653889/10000000000 : ℝ), (5181943171/10000000000 : ℝ)] ![(22593453658333/50000000000000 : ℝ), (11441018677873/100000000000000 : ℝ), (10843018497917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351835467/10000000000 : ℝ)|^4807 ≤ (22593453658333/50000000000000 : ℝ)^3783
        have hw : |(5351835467/10000000000 : ℝ)|=(5351835467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1815653889/10000000000 : ℝ)|^4807 ≤ (11441018677873/100000000000000 : ℝ)^3783
        have hw : |(-1815653889/10000000000 : ℝ)|=(1815653889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181943171/10000000000 : ℝ)|^4807 ≤ (10843018497917/25000000000000 : ℝ)^3783
        have hw : |(5181943171/10000000000 : ℝ)|=(5181943171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s4_2 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675917659/5000000000 : ℝ)*x 0 + (5181943359/10000000000 : ℝ)*x 1 + (-1815653839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675917659/5000000000 : ℝ)^4807 ≤ (5648363214761/12500000000000 : ℝ)^3783 := by
    have hnat : (2675917659 : ℕ)^4807*12500000000000^3783 ≤ 5648363214761^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675917659 5000000000 5648363214761 12500000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181943359/10000000000 : ℝ)^4807 ≤ (43372075991131/100000000000000 : ℝ)^3783 := by
    have hnat : (5181943359 : ℕ)^4807*100000000000000^3783 ≤ 43372075991131^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181943359 10000000000 43372075991131 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1815653839/10000000000 : ℝ)^4807 ≤ (2860254569381/25000000000000 : ℝ)^3783 := by
    have hnat : (1815653839 : ℕ)^4807*25000000000000^3783 ≤ 2860254569381^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815653839 10000000000 2860254569381 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675917659/5000000000 : ℝ), (5181943359/10000000000 : ℝ), (-1815653839/10000000000 : ℝ)] ![(5648363214761/12500000000000 : ℝ), (43372075991131/100000000000000 : ℝ), (2860254569381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675917659/5000000000 : ℝ)|^4807 ≤ (5648363214761/12500000000000 : ℝ)^3783
        have hw : |(2675917659/5000000000 : ℝ)|=(2675917659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181943359/10000000000 : ℝ)|^4807 ≤ (43372075991131/100000000000000 : ℝ)^3783
        have hw : |(5181943359/10000000000 : ℝ)|=(5181943359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1815653839/10000000000 : ℝ)|^4807 ≤ (2860254569381/25000000000000 : ℝ)^3783
        have hw : |(-1815653839/10000000000 : ℝ)|=(1815653839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s4_3 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4202764621/10000000000 : ℝ)*x 0 + (483941741/1250000000 : ℝ)*x 1 + (2277502753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202764621/10000000000 : ℝ)^4807 ≤ (33237763424731/100000000000000 : ℝ)^3783 := by
    have hnat : (4202764621 : ℕ)^4807*100000000000000^3783 ≤ 33237763424731^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202764621 10000000000 33237763424731 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483941741/1250000000 : ℝ)^4807 ≤ (14972673357531/50000000000000 : ℝ)^3783 := by
    have hnat : (483941741 : ℕ)^4807*50000000000000^3783 ≤ 14972673357531^3783*1250000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483941741 1250000000 14972673357531 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2277502753/5000000000 : ℝ)^4807 ≤ (2301055615693/6250000000000 : ℝ)^3783 := by
    have hnat : (2277502753 : ℕ)^4807*6250000000000^3783 ≤ 2301055615693^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277502753 5000000000 2301055615693 6250000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202764621/10000000000 : ℝ), (483941741/1250000000 : ℝ), (2277502753/5000000000 : ℝ)] ![(33237763424731/100000000000000 : ℝ), (14972673357531/50000000000000 : ℝ), (2301055615693/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202764621/10000000000 : ℝ)|^4807 ≤ (33237763424731/100000000000000 : ℝ)^3783
        have hw : |(4202764621/10000000000 : ℝ)|=(4202764621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(483941741/1250000000 : ℝ)|^4807 ≤ (14972673357531/50000000000000 : ℝ)^3783
        have hw : |(483941741/1250000000 : ℝ)|=(483941741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2277502753/5000000000 : ℝ)|^4807 ≤ (2301055615693/6250000000000 : ℝ)^3783
        have hw : |(2277502753/5000000000 : ℝ)|=(2277502753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s4_4 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418653037/2500000000 : ℝ)*x 0 + (2591994179/5000000000 : ℝ)*x 1 + (5453680019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418653037/2500000000 : ℝ)^4807 ≤ (206476075201/2000000000000 : ℝ)^3783 := by
    have hnat : (418653037 : ℕ)^4807*2000000000000^3783 ≤ 206476075201^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418653037 2500000000 206476075201 2000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591994179/5000000000 : ℝ)^4807 ≤ (4339382661021/10000000000000 : ℝ)^3783 := by
    have hnat : (2591994179 : ℕ)^4807*10000000000000^3783 ≤ 4339382661021^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591994179 5000000000 4339382661021 10000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453680019/10000000000 : ℝ)^4807 ≤ (46282369612551/100000000000000 : ℝ)^3783 := by
    have hnat : (5453680019 : ℕ)^4807*100000000000000^3783 ≤ 46282369612551^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453680019 10000000000 46282369612551 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418653037/2500000000 : ℝ), (2591994179/5000000000 : ℝ), (5453680019/10000000000 : ℝ)] ![(206476075201/2000000000000 : ℝ), (4339382661021/10000000000000 : ℝ), (46282369612551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418653037/2500000000 : ℝ)|^4807 ≤ (206476075201/2000000000000 : ℝ)^3783
        have hw : |(-418653037/2500000000 : ℝ)|=(418653037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591994179/5000000000 : ℝ)|^4807 ≤ (4339382661021/10000000000000 : ℝ)^3783
        have hw : |(2591994179/5000000000 : ℝ)|=(2591994179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453680019/10000000000 : ℝ)|^4807 ≤ (46282369612551/100000000000000 : ℝ)^3783
        have hw : |(5453680019/10000000000 : ℝ)|=(5453680019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s4_5 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278971591/10000000000 : ℝ)*x 0 + (-771958453/5000000000 : ℝ)*x 1 + (1090736033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278971591/10000000000 : ℝ)^4807 ≤ (22203308466269/50000000000000 : ℝ)^3783 := by
    have hnat : (5278971591 : ℕ)^4807*50000000000000^3783 ≤ 22203308466269^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278971591 10000000000 22203308466269 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771958453/5000000000 : ℝ)^4807 ≤ (4655505931217/50000000000000 : ℝ)^3783 := by
    have hnat : (771958453 : ℕ)^4807*50000000000000^3783 ≤ 4655505931217^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771958453 5000000000 4655505931217 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090736033/2000000000 : ℝ)^4807 ≤ (11570592796739/25000000000000 : ℝ)^3783 := by
    have hnat : (1090736033 : ℕ)^4807*25000000000000^3783 ≤ 11570592796739^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090736033 2000000000 11570592796739 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278971591/10000000000 : ℝ), (-771958453/5000000000 : ℝ), (1090736033/2000000000 : ℝ)] ![(22203308466269/50000000000000 : ℝ), (4655505931217/50000000000000 : ℝ), (11570592796739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278971591/10000000000 : ℝ)|^4807 ≤ (22203308466269/50000000000000 : ℝ)^3783
        have hw : |(5278971591/10000000000 : ℝ)|=(5278971591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-771958453/5000000000 : ℝ)|^4807 ≤ (4655505931217/50000000000000 : ℝ)^3783
        have hw : |(-771958453/5000000000 : ℝ)|=(771958453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090736033/2000000000 : ℝ)|^4807 ≤ (11570592796739/25000000000000 : ℝ)^3783
        have hw : |(1090736033/2000000000 : ℝ)|=(1090736033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s4_6 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278971603/10000000000 : ℝ)*x 0 + (5453680091/10000000000 : ℝ)*x 1 + (-308783399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278971603/10000000000 : ℝ)^4807 ≤ (8881323412161/20000000000000 : ℝ)^3783 := by
    have hnat : (5278971603 : ℕ)^4807*20000000000000^3783 ≤ 8881323412161^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278971603 10000000000 8881323412161 20000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453680091/10000000000 : ℝ)^4807 ≤ (4628237038897/10000000000000 : ℝ)^3783 := by
    have hnat : (5453680091 : ℕ)^4807*10000000000000^3783 ≤ 4628237038897^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453680091 10000000000 4628237038897 10000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (308783399/2000000000 : ℝ)^4807 ≤ (465550627223/5000000000000 : ℝ)^3783 := by
    have hnat : (308783399 : ℕ)^4807*5000000000000^3783 ≤ 465550627223^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308783399 2000000000 465550627223 5000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278971603/10000000000 : ℝ), (5453680091/10000000000 : ℝ), (-308783399/2000000000 : ℝ)] ![(8881323412161/20000000000000 : ℝ), (4628237038897/10000000000000 : ℝ), (465550627223/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278971603/10000000000 : ℝ)|^4807 ≤ (8881323412161/20000000000000 : ℝ)^3783
        have hw : |(5278971603/10000000000 : ℝ)|=(5278971603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453680091/10000000000 : ℝ)|^4807 ≤ (4628237038897/10000000000000 : ℝ)^3783
        have hw : |(5453680091/10000000000 : ℝ)|=(5453680091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-308783399/2000000000 : ℝ)|^4807 ≤ (465550627223/5000000000000 : ℝ)^3783
        have hw : |(-308783399/2000000000 : ℝ)|=(308783399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s4_7 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168117393/400000000 : ℝ)*x 0 + (4549900809/10000000000 : ℝ)*x 1 + (3876692513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168117393/400000000 : ℝ)^4807 ≤ (1661973693001/5000000000000 : ℝ)^3783 := by
    have hnat : (168117393 : ℕ)^4807*5000000000000^3783 ≤ 1661973693001^3783*400000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168117393 400000000 1661973693001 5000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4549900809/10000000000 : ℝ)^4807 ≤ (36764469485337/100000000000000 : ℝ)^3783 := by
    have hnat : (4549900809 : ℕ)^4807*100000000000000^3783 ≤ 36764469485337^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549900809 10000000000 36764469485337 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3876692513/10000000000 : ℝ)^4807 ≤ (29996056636111/100000000000000 : ℝ)^3783 := by
    have hnat : (3876692513 : ℕ)^4807*100000000000000^3783 ≤ 29996056636111^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3876692513 10000000000 29996056636111 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168117393/400000000 : ℝ), (4549900809/10000000000 : ℝ), (3876692513/10000000000 : ℝ)] ![(1661973693001/5000000000000 : ℝ), (36764469485337/100000000000000 : ℝ), (29996056636111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168117393/400000000 : ℝ)|^4807 ≤ (1661973693001/5000000000000 : ℝ)^3783
        have hw : |(168117393/400000000 : ℝ)|=(168117393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4549900809/10000000000 : ℝ)|^4807 ≤ (36764469485337/100000000000000 : ℝ)^3783
        have hw : |(4549900809/10000000000 : ℝ)|=(4549900809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3876692513/10000000000 : ℝ)|^4807 ≤ (29996056636111/100000000000000 : ℝ)^3783
        have hw : |(3876692513/10000000000 : ℝ)|=(3876692513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1622_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10511/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16321/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1633/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1633/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1633/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1633/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1633/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1633/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10503/100000 : ℝ) ^ (4803/1024 : ℝ) ≤ (102706787647981/4000000000000000000 : ℝ) := by
    have hpowers : (10503/100000 : ℝ)^4803 ≤ (102706787647981/4000000000000000000 : ℝ)^1024 := by
      have hnat : (10503 : ℕ)^4803*4000000000000000000^1024 ≤ 102706787647981^1024*100000^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10503 100000 102706787647981 4000000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10503/100000 : ℝ)) (X := (102706787647981/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1633/10000 : ℝ) ^ (4803/1024 : ℝ) ≤ (20350122901078471/100000000000000000000 : ℝ) := by
    have hpowers : (1633/10000 : ℝ)^4803 ≤ (20350122901078471/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1633 : ℕ)^4803*100000000000000000000^1024 ≤ 20350122901078471^1024*10000^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1633 10000 20350122901078471 100000000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1633/10000 : ℝ)) (X := (20350122901078471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000102706787647981/2000000000000000000 : ℝ) ≤ (10000109483266597/10000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (2000102706787647981/2000000000000000000 : ℝ)^1024 ≤ (10000109483266597/10000000000000000 : ℝ)^4803 := by
      have hnat : (2000102706787647981 : ℕ)^1024*10000000000000000^4803 ≤ 10000109483266597^4803*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000102706787647981 2000000000000000000 10000109483266597 10000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000109483266597/10000000000000000 : ℝ)) (X := (2000102706787647981/2000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25005729448148069499/25000000000000000000 : ℝ) ≤ (5000244281741389/5000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (25005729448148069499/25000000000000000000 : ℝ)^1024 ≤ (5000244281741389/5000000000000000 : ℝ)^4803 := by
      have hnat : (25005729448148069499 : ℕ)^1024*5000000000000000^4803 ≤ 5000244281741389^4803*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005729448148069499 25000000000000000000 5000244281741389 5000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000244281741389/5000000000000000 : ℝ)) (X := (25005729448148069499/25000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020350122901078471/50000000000000000000 : ℝ) ≤ (10000867643698959/10000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (50020350122901078471/50000000000000000000 : ℝ)^1024 ≤ (10000867643698959/10000000000000000 : ℝ)^4803 := by
      have hnat : (50020350122901078471 : ℕ)^1024*10000000000000000^4803 ≤ 10000867643698959^4803*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020350122901078471 50000000000000000000 10000867643698959 10000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000867643698959/10000000000000000 : ℝ)) (X := (50020350122901078471/50000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(102706787647981/4000000000000000000 : ℝ) ≤ ((58262674999973362633/58270000000000000000 : ℝ)+2*(379080216181/582700000000000 : ℝ)*(10503/100000 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (58262674999973362633/58270000000000000000 : ℝ)+2*(379080216181/582700000000000 : ℝ)*(10503/100000 : ℝ)=(10000109483266597/10000000000000000 : ℝ) by norm_num, show 1+2*(102706787647981/4000000000000000000 : ℝ)=(2000102706787647981/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20350122901078471/100000000000000000000 : ℝ)+(102706787647981/4000000000000000000 : ℝ) ≤ ((58262674999973362633/58270000000000000000 : ℝ)+(379080216181/582700000000000 : ℝ)*((1633/10000 : ℝ)+(10503/100000 : ℝ)))^(4803/1024 : ℝ) := by
    rw [show (58262674999973362633/58270000000000000000 : ℝ)+(379080216181/582700000000000 : ℝ)*((1633/10000 : ℝ)+(10503/100000 : ℝ))=(5000244281741389/5000000000000000 : ℝ) by norm_num, show 1+(20350122901078471/100000000000000000000 : ℝ)+(102706787647981/4000000000000000000 : ℝ)=(25005729448148069499/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20350122901078471/100000000000000000000 : ℝ) ≤ ((58262674999973362633/58270000000000000000 : ℝ)+2*(379080216181/582700000000000 : ℝ)*(1633/10000 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (58262674999973362633/58270000000000000000 : ℝ)+2*(379080216181/582700000000000 : ℝ)*(1633/10000 : ℝ)=(10000867643698959/10000000000000000 : ℝ) by norm_num, show 1+2*(20350122901078471/100000000000000000000 : ℝ)=(50020350122901078471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58262674999973362633/58270000000000000000 : ℝ)*(X 1 0+X 2 0)+(379080216181/582700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (10503/100000 : ℝ)) (hi := (1633/10000 : ℝ)) (c := (58262674999973362633/58270000000000000000 : ℝ)) (alpha := (379080216181/582700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58262674999973362633/58270000000000000000 : ℝ)*(X 0 1+X 2 1)+(379080216181/582700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (10503/100000 : ℝ)) (hi := (1633/10000 : ℝ)) (c := (58262674999973362633/58270000000000000000 : ℝ)) (alpha := (379080216181/582700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58262674999973362633/58270000000000000000 : ℝ)*(X 0 2+X 1 2)+(379080216181/582700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (10503/100000 : ℝ)) (hi := (1633/10000 : ℝ)) (c := (58262674999973362633/58270000000000000000 : ℝ)) (alpha := (379080216181/582700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1674543799/10000000000 : ℝ)*X 0 0+(545574643/1000000000 : ℝ)*X 0 1+(323871469/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351835467/10000000000 : ℝ)*X 1 0+(-1815653889/10000000000 : ℝ)*X 1 1+(5181943171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675917659/5000000000 : ℝ)*X 2 0+(5181943359/10000000000 : ℝ)*X 2 1+(-1815653839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4202764621/10000000000 : ℝ)*X 0 0+(483941741/1250000000 : ℝ)*X 0 1+(2277502753/5000000000 : ℝ)*X 0 2+(4202764621/10000000000 : ℝ)*X 1 0+(483941741/1250000000 : ℝ)*X 1 1+(2277502753/5000000000 : ℝ)*X 1 2+(4202764621/10000000000 : ℝ)*X 2 0+(483941741/1250000000 : ℝ)*X 2 1+(2277502753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-418653037/2500000000 : ℝ)*X 0 0+(2591994179/5000000000 : ℝ)*X 0 1+(5453680019/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278971591/10000000000 : ℝ)*X 1 0+(-771958453/5000000000 : ℝ)*X 1 1+(1090736033/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278971603/10000000000 : ℝ)*X 2 0+(5453680091/10000000000 : ℝ)*X 2 1+(-308783399/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((168117393/400000000 : ℝ)*X 0 0+(4549900809/10000000000 : ℝ)*X 0 1+(3876692513/10000000000 : ℝ)*X 0 2+(168117393/400000000 : ℝ)*X 1 0+(4549900809/10000000000 : ℝ)*X 1 1+(3876692513/10000000000 : ℝ)*X 1 2+(168117393/400000000 : ℝ)*X 2 0+(4549900809/10000000000 : ℝ)*X 2 1+(3876692513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13985618002325660617470974799/1456750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33932743/2000000000000 : ℝ)*(base19) + (1464832453/100000000000000 : ℝ)*(base23) + (8704857/12500000000000 : ℝ)*(lower2) + (229110273/100000000000000 : ℝ)*(upper3) + (157957259/100000000000000 : ℝ)*(upper5) + (1278858024496899/50000000000000 : ℝ)*(major0) + (1278858024496899/50000000000000 : ℝ)*(major1) + (1278858024496899/50000000000000 : ℝ)*(major2) + (3652279864127283/100000000000000 : ℝ)*(sp0) + (730459068573041/20000000000000 : ℝ)*(sp1) + (1826147787334951/50000000000000 : ℝ)*(sp2) + (182890784413747/12500000000000 : ℝ)*(sp3) + (536730471/3125000000000 : ℝ)*(sp4) + (132236821/1562500000000 : ℝ)*(sp7) + (36578368461663/2500000000000 : ℝ)*(f.failure) + (730459407900471/20000000000000 : ℝ)*(f.sum) + (46448171573167/29135000000000000000000000000 : ℝ)*base66 + (4854257060032124933/2913500000000000000000000000000000 : ℝ)*base68 + (5874946651654875067/2913500000000000000000000000000000 : ℝ)*base69 + (18009555563464375067/2913500000000000000000000000000000 : ℝ)*base71 + (173349057018727/29135000000000000000000000000 : ℝ)*base74 + (15037440744912375067/2913500000000000000000000000000000 : ℝ)*base75 + (23265587933700875067/2913500000000000000000000000000000 : ℝ)*base77 + (6199767742084124933/2913500000000000000000000000000000 : ℝ)*base80 + (7685868759953/7283750000000000000000000000 : ℝ)*base82 + (135387/125000000000000000000 : ℝ)*base89 + (135387/125000000000000000000 : ℝ)*base91 + (135387/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4119051228420378770490766671/364187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (945854741/50000000000000 : ℝ)*(base19) + (241612817/12500000000000 : ℝ)*(base23) + (333369741/50000000000000 : ℝ)*(lower1) + (242787801/100000000000000 : ℝ)*(upper3) + (2317543/12500000000000 : ℝ)*(lower4) + (209300357/100000000000000 : ℝ)*(upper5) + (324582958920071/12500000000000 : ℝ)*(major0) + (324582958920071/12500000000000 : ℝ)*(major1) + (324582958920071/12500000000000 : ℝ)*(major2) + (170748627/100000000000000 : ℝ)*(sp1) + (115872260697259/3125000000000 : ℝ)*(sp4) + (185395513992709/5000000000000 : ℝ)*(sp5) + (3707910409409753/100000000000000 : ℝ)*(sp6) + (1485414623400547/100000000000000 : ℝ)*(sp7) + (1485414623400547/100000000000000 : ℝ)*(f.failure) + (115872260697259/3125000000000 : ℝ)*(f.sum) + (127951669006077/29135000000000000000000000000 : ℝ)*base66 + (4511738018464081943/728375000000000000000000000000000 : ℝ)*base67 + (6758561875825081943/728375000000000000000000000000000 : ℝ)*base69 + (1848445473560793057/728375000000000000000000000000000 : ℝ)*base72 + (6805124345051/3641875000000000000000000000 : ℝ)*base73 + (7578098509948206943/728375000000000000000000000000000 : ℝ)*base75 + (835259592377956943/728375000000000000000000000000000 : ℝ)*base77 + (736192507725043057/728375000000000000000000000000000 : ℝ)*base80 + (5544098779753/1820937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (22674097/5000000000000000000000 : ℝ)*base90 + (22674097/5000000000000000000000 : ℝ)*base92 + (22674097/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1622_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10511/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16321/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1622_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1622_s5_0 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1674550723/10000000000 : ℝ)*x 0 + (1363928217/2500000000 : ℝ)*x 1 + (2590986219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674550723/10000000000 : ℝ)^4807 ≤ (5161661290731/50000000000000 : ℝ)^3783 := by
    have hnat : (1674550723 : ℕ)^4807*50000000000000^3783 ≤ 5161661290731^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674550723 10000000000 5161661290731 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363928217/2500000000 : ℝ)^4807 ≤ (23152146073/50000000000 : ℝ)^3783 := by
    have hnat : (1363928217 : ℕ)^4807*50000000000^3783 ≤ 23152146073^3783*2500000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363928217 2500000000 23152146073 50000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590986219/5000000000 : ℝ)^4807 ≤ (43372385259231/100000000000000 : ℝ)^3783 := by
    have hnat : (2590986219 : ℕ)^4807*100000000000000^3783 ≤ 43372385259231^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590986219 5000000000 43372385259231 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1674550723/10000000000 : ℝ), (1363928217/2500000000 : ℝ), (2590986219/5000000000 : ℝ)] ![(5161661290731/50000000000000 : ℝ), (23152146073/50000000000 : ℝ), (43372385259231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1674550723/10000000000 : ℝ)|^4807 ≤ (5161661290731/50000000000000 : ℝ)^3783
        have hw : |(-1674550723/10000000000 : ℝ)|=(1674550723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363928217/2500000000 : ℝ)|^4807 ≤ (23152146073/50000000000 : ℝ)^3783
        have hw : |(1363928217/2500000000 : ℝ)|=(1363928217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590986219/5000000000 : ℝ)|^4807 ≤ (43372385259231/100000000000000 : ℝ)^3783
        have hw : |(2590986219/5000000000 : ℝ)|=(2590986219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s5_1 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070365263/2000000000 : ℝ)*x 0 + (-1815627309/10000000000 : ℝ)*x 1 + (2590986207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070365263/2000000000 : ℝ)^4807 ≤ (45186809127503/100000000000000 : ℝ)^3783 := by
    have hnat : (1070365263 : ℕ)^4807*100000000000000^3783 ≤ 45186809127503^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070365263 2000000000 45186809127503 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1815627309/10000000000 : ℝ)^4807 ≤ (11440805852439/100000000000000 : ℝ)^3783 := by
    have hnat : (1815627309 : ℕ)^4807*100000000000000^3783 ≤ 11440805852439^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815627309 10000000000 11440805852439 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590986207/5000000000 : ℝ)^4807 ≤ (2168619250199/5000000000000 : ℝ)^3783 := by
    have hnat : (2590986207 : ℕ)^4807*5000000000000^3783 ≤ 2168619250199^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590986207 5000000000 2168619250199 5000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070365263/2000000000 : ℝ), (-1815627309/10000000000 : ℝ), (2590986207/5000000000 : ℝ)] ![(45186809127503/100000000000000 : ℝ), (11440805852439/100000000000000 : ℝ), (2168619250199/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070365263/2000000000 : ℝ)|^4807 ≤ (45186809127503/100000000000000 : ℝ)^3783
        have hw : |(1070365263/2000000000 : ℝ)|=(1070365263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1815627309/10000000000 : ℝ)|^4807 ≤ (11440805852439/100000000000000 : ℝ)^3783
        have hw : |(-1815627309/10000000000 : ℝ)|=(1815627309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590986207/5000000000 : ℝ)|^4807 ≤ (2168619250199/5000000000000 : ℝ)^3783
        have hw : |(2590986207/5000000000 : ℝ)|=(2590986207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s5_2 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675913103/5000000000 : ℝ)*x 0 + (5181972451/10000000000 : ℝ)*x 1 + (-1815627407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675913103/5000000000 : ℝ)^4807 ≤ (22593403979037/50000000000000 : ℝ)^3783 := by
    have hnat : (2675913103 : ℕ)^4807*50000000000000^3783 ≤ 22593403979037^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675913103 5000000000 22593403979037 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181972451/10000000000 : ℝ)^4807 ≤ (10843096349373/25000000000000 : ℝ)^3783 := by
    have hnat : (5181972451 : ℕ)^4807*25000000000000^3783 ≤ 10843096349373^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181972451 10000000000 10843096349373 25000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1815627407/10000000000 : ℝ)^4807 ≤ (5720403318561/50000000000000 : ℝ)^3783 := by
    have hnat : (1815627407 : ℕ)^4807*50000000000000^3783 ≤ 5720403318561^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815627407 10000000000 5720403318561 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675913103/5000000000 : ℝ), (5181972451/10000000000 : ℝ), (-1815627407/10000000000 : ℝ)] ![(22593403979037/50000000000000 : ℝ), (10843096349373/25000000000000 : ℝ), (5720403318561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675913103/5000000000 : ℝ)|^4807 ≤ (22593403979037/50000000000000 : ℝ)^3783
        have hw : |(2675913103/5000000000 : ℝ)|=(2675913103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181972451/10000000000 : ℝ)|^4807 ≤ (10843096349373/25000000000000 : ℝ)^3783
        have hw : |(5181972451/10000000000 : ℝ)|=(5181972451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1815627407/10000000000 : ℝ)|^4807 ≤ (5720403318561/50000000000000 : ℝ)^3783
        have hw : |(-1815627407/10000000000 : ℝ)|=(1815627407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s5_3 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52534613/125000000 : ℝ)*x 0 + (1935805969/5000000000 : ℝ)*x 1 + (455492653/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52534613/125000000 : ℝ)^4807 ≤ (1661890391623/5000000000000 : ℝ)^3783 := by
    have hnat : (52534613 : ℕ)^4807*5000000000000^3783 ≤ 1661890391623^3783*125000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52534613 125000000 1661890391623 5000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1935805969/5000000000 : ℝ)^4807 ≤ (1871632089551/6250000000000 : ℝ)^3783 := by
    have hnat : (1935805969 : ℕ)^4807*6250000000000^3783 ≤ 1871632089551^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935805969 5000000000 1871632089551 6250000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455492653/1000000000 : ℝ)^4807 ≤ (143812807507/390625000000 : ℝ)^3783 := by
    have hnat : (455492653 : ℕ)^4807*390625000000^3783 ≤ 143812807507^3783*1000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455492653 1000000000 143812807507 390625000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52534613/125000000 : ℝ), (1935805969/5000000000 : ℝ), (455492653/1000000000 : ℝ)] ![(1661890391623/5000000000000 : ℝ), (1871632089551/6250000000000 : ℝ), (143812807507/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52534613/125000000 : ℝ)|^4807 ≤ (1661890391623/5000000000000 : ℝ)^3783
        have hw : |(52534613/125000000 : ℝ)|=(52534613/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1935805969/5000000000 : ℝ)|^4807 ≤ (1871632089551/6250000000000 : ℝ)^3783
        have hw : |(1935805969/5000000000 : ℝ)|=(1935805969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(455492653/1000000000 : ℝ)|^4807 ≤ (143812807507/390625000000 : ℝ)^3783
        have hw : |(455492653/1000000000 : ℝ)|=(455492653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s5_4 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-837309419/5000000000 : ℝ)*x 0 + (5184016711/10000000000 : ℝ)*x 1 + (681705899/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837309419/5000000000 : ℝ)^4807 ≤ (1032385616709/10000000000000 : ℝ)^3783 := by
    have hnat : (837309419 : ℕ)^4807*10000000000000^3783 ≤ 1032385616709^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837309419 5000000000 1032385616709 10000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184016711/10000000000 : ℝ)^4807 ≤ (43394128189179/100000000000000 : ℝ)^3783 := by
    have hnat : (5184016711 : ℕ)^4807*100000000000000^3783 ≤ 43394128189179^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184016711 10000000000 43394128189179 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681705899/1250000000 : ℝ)^4807 ≤ (723156494057/1562500000000 : ℝ)^3783 := by
    have hnat : (681705899 : ℕ)^4807*1562500000000^3783 ≤ 723156494057^3783*1250000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681705899 1250000000 723156494057 1562500000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-837309419/5000000000 : ℝ), (5184016711/10000000000 : ℝ), (681705899/1250000000 : ℝ)] ![(1032385616709/10000000000000 : ℝ), (43394128189179/100000000000000 : ℝ), (723156494057/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-837309419/5000000000 : ℝ)|^4807 ≤ (1032385616709/10000000000000 : ℝ)^3783
        have hw : |(-837309419/5000000000 : ℝ)|=(837309419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184016711/10000000000 : ℝ)|^4807 ≤ (43394128189179/100000000000000 : ℝ)^3783
        have hw : |(5184016711/10000000000 : ℝ)|=(5184016711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681705899/1250000000 : ℝ)|^4807 ≤ (723156494057/1562500000000 : ℝ)^3783
        have hw : |(681705899/1250000000 : ℝ)|=(681705899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s5_5 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639489601/5000000000 : ℝ)*x 0 + (-1543952479/10000000000 : ℝ)*x 1 + (2726823671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639489601/5000000000 : ℝ)^4807 ≤ (22203349143179/50000000000000 : ℝ)^3783 := by
    have hnat : (2639489601 : ℕ)^4807*50000000000000^3783 ≤ 22203349143179^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639489601 5000000000 22203349143179 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1543952479/10000000000 : ℝ)^4807 ≤ (9311284466661/100000000000000 : ℝ)^3783 := by
    have hnat : (1543952479 : ℕ)^4807*100000000000000^3783 ≤ 9311284466661^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543952479 10000000000 9311284466661 100000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726823671/5000000000 : ℝ)^4807 ≤ (9256403447437/20000000000000 : ℝ)^3783 := by
    have hnat : (2726823671 : ℕ)^4807*20000000000000^3783 ≤ 9256403447437^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726823671 5000000000 9256403447437 20000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639489601/5000000000 : ℝ), (-1543952479/10000000000 : ℝ), (2726823671/5000000000 : ℝ)] ![(22203349143179/50000000000000 : ℝ), (9311284466661/100000000000000 : ℝ), (9256403447437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639489601/5000000000 : ℝ)|^4807 ≤ (22203349143179/50000000000000 : ℝ)^3783
        have hw : |(2639489601/5000000000 : ℝ)|=(2639489601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1543952479/10000000000 : ℝ)|^4807 ≤ (9311284466661/100000000000000 : ℝ)^3783
        have hw : |(-1543952479/10000000000 : ℝ)|=(1543952479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726823671/5000000000 : ℝ)|^4807 ≤ (9256403447437/20000000000000 : ℝ)^3783
        have hw : |(2726823671/5000000000 : ℝ)|=(2726823671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s5_6 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639489427/5000000000 : ℝ)*x 0 + (5453647573/10000000000 : ℝ)*x 1 + (-1543952639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639489427/5000000000 : ℝ)^4807 ≤ (693854602603/1562500000000 : ℝ)^3783 := by
    have hnat : (2639489427 : ℕ)^4807*1562500000000^3783 ≤ 693854602603^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639489427 5000000000 693854602603 1562500000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453647573/10000000000 : ℝ)^4807 ≤ (723156558253/1562500000000 : ℝ)^3783 := by
    have hnat : (5453647573 : ℕ)^4807*1562500000000^3783 ≤ 723156558253^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453647573 10000000000 723156558253 1562500000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1543952639/10000000000 : ℝ)^4807 ≤ (4655642846391/50000000000000 : ℝ)^3783 := by
    have hnat : (1543952639 : ℕ)^4807*50000000000000^3783 ≤ 4655642846391^3783*10000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543952639 10000000000 4655642846391 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639489427/5000000000 : ℝ), (5453647573/10000000000 : ℝ), (-1543952639/10000000000 : ℝ)] ![(693854602603/1562500000000 : ℝ), (723156558253/1562500000000 : ℝ), (4655642846391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639489427/5000000000 : ℝ)|^4807 ≤ (693854602603/1562500000000 : ℝ)^3783
        have hw : |(2639489427/5000000000 : ℝ)|=(2639489427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453647573/10000000000 : ℝ)|^4807 ≤ (723156558253/1562500000000 : ℝ)^3783
        have hw : |(5453647573/10000000000 : ℝ)|=(5453647573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1543952639/10000000000 : ℝ)|^4807 ≤ (4655642846391/50000000000000 : ℝ)^3783
        have hw : |(-1543952639/10000000000 : ℝ)|=(1543952639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1622_s5_7 (p : ℝ) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (840587833/2000000000 : ℝ)*x 0 + (2274912313/5000000000 : ℝ)*x 1 + (775353527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840587833/2000000000 : ℝ)^4807 ≤ (6647903494867/20000000000000 : ℝ)^3783 := by
    have hnat : (840587833 : ℕ)^4807*20000000000000^3783 ≤ 6647903494867^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840587833 2000000000 6647903494867 20000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2274912313/5000000000 : ℝ)^4807 ≤ (18381843639579/50000000000000 : ℝ)^3783 := by
    have hnat : (2274912313 : ℕ)^4807*50000000000000^3783 ≤ 18381843639579^3783*5000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274912313 5000000000 18381843639579 50000000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (775353527/2000000000 : ℝ)^4807 ≤ (1874799702211/6250000000000 : ℝ)^3783 := by
    have hnat : (775353527 : ℕ)^4807*6250000000000^3783 ≤ 1874799702211^3783*2000000000^4807 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775353527 2000000000 1874799702211 6250000000000 4807 3783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4807/1024 : ℝ)) 4807 3783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840587833/2000000000 : ℝ), (2274912313/5000000000 : ℝ), (775353527/2000000000 : ℝ)] ![(6647903494867/20000000000000 : ℝ), (18381843639579/50000000000000 : ℝ), (1874799702211/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840587833/2000000000 : ℝ)|^4807 ≤ (6647903494867/20000000000000 : ℝ)^3783
        have hw : |(840587833/2000000000 : ℝ)|=(840587833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2274912313/5000000000 : ℝ)|^4807 ≤ (18381843639579/50000000000000 : ℝ)^3783
        have hw : |(2274912313/5000000000 : ℝ)|=(2274912313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(775353527/2000000000 : ℝ)|^4807 ≤ (1874799702211/6250000000000 : ℝ)^3783
        have hw : |(775353527/2000000000 : ℝ)|=(775353527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1622_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16321/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10511/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (657/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (102/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16321/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10511/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16321/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10511/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16321/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10511/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16321/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10511/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16321/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10511/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16321/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10511/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10511/100000 : ℝ) ^ (4803/1024 : ℝ) ≤ (2576855952292441/100000000000000000000 : ℝ) := by
    have hpowers : (10511/100000 : ℝ)^4803 ≤ (2576855952292441/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10511 : ℕ)^4803*100000000000000000000^1024 ≤ 2576855952292441^1024*100000^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10511 100000 2576855952292441 100000000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10511/100000 : ℝ)) (X := (2576855952292441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16321/100000 : ℝ) ^ (4803/1024 : ℝ) ≤ (2029757028679087/10000000000000000000 : ℝ) := by
    have hpowers : (16321/100000 : ℝ)^4803 ≤ (2029757028679087/10000000000000000000 : ℝ)^1024 := by
      have hnat : (16321 : ℕ)^4803*10000000000000000000^1024 ≤ 2029757028679087^1024*100000^4803 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16321 100000 2029757028679087 10000000000000000000 4803 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16321/100000 : ℝ)) (X := (2029757028679087/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002576855952292441/50000000000000000000 : ℝ) ≤ (2500027468738267/2500000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (50002576855952292441/50000000000000000000 : ℝ)^1024 ≤ (2500027468738267/2500000000000000 : ℝ)^4803 := by
      have hnat : (50002576855952292441 : ℕ)^1024*2500000000000000^4803 ≤ 2500027468738267^4803*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002576855952292441 50000000000000000000 2500027468738267 2500000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500027468738267/2500000000000000 : ℝ)) (X := (50002576855952292441/50000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022874426239083311/100000000000000000000 : ℝ) ≤ (10000487639078291/10000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (100022874426239083311/100000000000000000000 : ℝ)^1024 ≤ (10000487639078291/10000000000000000 : ℝ)^4803 := by
      have hnat : (100022874426239083311 : ℕ)^1024*10000000000000000^4803 ≤ 10000487639078291^4803*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022874426239083311 100000000000000000000 10000487639078291 10000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000487639078291/10000000000000000 : ℝ)) (X := (100022874426239083311/100000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002029757028679087/5000000000000000000 : ℝ) ≤ (5000432701601757/5000000000000000 : ℝ) ^ (4803/1024 : ℝ) := by
    have hpowers : (5002029757028679087/5000000000000000000 : ℝ)^1024 ≤ (5000432701601757/5000000000000000 : ℝ)^4803 := by
      have hnat : (5002029757028679087 : ℕ)^1024*5000000000000000^4803 ≤ 5000432701601757^4803*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002029757028679087 5000000000000000000 5000432701601757 5000000000000000 1024 4803 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000432701601757/5000000000000000 : ℝ)) (X := (5002029757028679087/5000000000000000000 : ℝ)) (by norm_num) 4803 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2576855952292441/100000000000000000000 : ℝ) ≤ ((29046348508018443587/29050000000000000000 : ℝ)+2*(377764125223/581000000000000 : ℝ)*(10511/100000 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (29046348508018443587/29050000000000000000 : ℝ)+2*(377764125223/581000000000000 : ℝ)*(10511/100000 : ℝ)=(2500027468738267/2500000000000000 : ℝ) by norm_num, show 1+2*(2576855952292441/100000000000000000000 : ℝ)=(50002576855952292441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2029757028679087/10000000000000000000 : ℝ)+(2576855952292441/100000000000000000000 : ℝ) ≤ ((29046348508018443587/29050000000000000000 : ℝ)+(377764125223/581000000000000 : ℝ)*((16321/100000 : ℝ)+(10511/100000 : ℝ)))^(4803/1024 : ℝ) := by
    rw [show (29046348508018443587/29050000000000000000 : ℝ)+(377764125223/581000000000000 : ℝ)*((16321/100000 : ℝ)+(10511/100000 : ℝ))=(10000487639078291/10000000000000000 : ℝ) by norm_num, show 1+(2029757028679087/10000000000000000000 : ℝ)+(2576855952292441/100000000000000000000 : ℝ)=(100022874426239083311/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2029757028679087/10000000000000000000 : ℝ) ≤ ((29046348508018443587/29050000000000000000 : ℝ)+2*(377764125223/581000000000000 : ℝ)*(16321/100000 : ℝ))^(4803/1024 : ℝ) := by
    rw [show (29046348508018443587/29050000000000000000 : ℝ)+2*(377764125223/581000000000000 : ℝ)*(16321/100000 : ℝ)=(5000432701601757/5000000000000000 : ℝ) by norm_num, show 1+2*(2029757028679087/10000000000000000000 : ℝ)=(5002029757028679087/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29046348508018443587/29050000000000000000 : ℝ)*(X 1 0+X 2 0)+(377764125223/581000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (10511/100000 : ℝ)) (hi := (16321/100000 : ℝ)) (c := (29046348508018443587/29050000000000000000 : ℝ)) (alpha := (377764125223/581000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29046348508018443587/29050000000000000000 : ℝ)*(X 0 1+X 2 1)+(377764125223/581000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (10511/100000 : ℝ)) (hi := (16321/100000 : ℝ)) (c := (29046348508018443587/29050000000000000000 : ℝ)) (alpha := (377764125223/581000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29046348508018443587/29050000000000000000 : ℝ)*(X 0 2+X 1 2)+(377764125223/581000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4803/1024 : ℝ)) (lo := (10511/100000 : ℝ)) (hi := (16321/100000 : ℝ)) (c := (29046348508018443587/29050000000000000000 : ℝ)) (alpha := (377764125223/581000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1674550723/10000000000 : ℝ)*X 0 0+(1363928217/2500000000 : ℝ)*X 0 1+(2590986219/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070365263/2000000000 : ℝ)*X 1 0+(-1815627309/10000000000 : ℝ)*X 1 1+(2590986207/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675913103/5000000000 : ℝ)*X 2 0+(5181972451/10000000000 : ℝ)*X 2 1+(-1815627407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((52534613/125000000 : ℝ)*X 0 0+(1935805969/5000000000 : ℝ)*X 0 1+(455492653/1000000000 : ℝ)*X 0 2+(52534613/125000000 : ℝ)*X 1 0+(1935805969/5000000000 : ℝ)*X 1 1+(455492653/1000000000 : ℝ)*X 1 2+(52534613/125000000 : ℝ)*X 2 0+(1935805969/5000000000 : ℝ)*X 2 1+(455492653/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-837309419/5000000000 : ℝ)*X 0 0+(5184016711/10000000000 : ℝ)*X 0 1+(681705899/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639489601/5000000000 : ℝ)*X 1 0+(-1543952479/10000000000 : ℝ)*X 1 1+(2726823671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639489427/5000000000 : ℝ)*X 2 0+(5453647573/10000000000 : ℝ)*X 2 1+(-1543952639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((840587833/2000000000 : ℝ)*X 0 0+(2274912313/5000000000 : ℝ)*X 0 1+(775353527/2000000000 : ℝ)*X 0 2+(840587833/2000000000 : ℝ)*X 1 0+(2274912313/5000000000 : ℝ)*X 1 1+(775353527/2000000000 : ℝ)*X 1 2+(840587833/2000000000 : ℝ)*X 2 0+(2274912313/5000000000 : ℝ)*X 2 1+(775353527/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1622_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (800484945252729815899788921/145250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (514005461/50000000000000 : ℝ)*(base19) + (926126557/100000000000000 : ℝ)*(base23) + (7353871/50000000000000 : ℝ)*(lower2) + (185963987/100000000000000 : ℝ)*(upper3) + (40206107/50000000000000 : ℝ)*(upper5) + (255829245904187/10000000000000 : ℝ)*(major0) + (255829245904187/10000000000000 : ℝ)*(major1) + (255829245904187/10000000000000 : ℝ)*(major2) + (456638649821887/12500000000000 : ℝ)*(sp0) + (1826559617025789/50000000000000 : ℝ)*(sp1) + (1826559667967971/50000000000000 : ℝ)*(sp2) + (1463459207288659/100000000000000 : ℝ)*(sp3) + (2765871851/25000000000000 : ℝ)*(sp4) + (210601191/4000000000000 : ℝ)*(sp7) + (731732236159217/50000000000000 : ℝ)*(f.failure) + (58449924193/1600000000 : ℝ)*(f.sum) + (4324530805087/1452500000000000000000000000 : ℝ)*base66 + (2836994692790351231/290500000000000000000000000000000 : ℝ)*base68 + (1318445202993851231/290500000000000000000000000000000 : ℝ)*base70 + (3098716728900851231/290500000000000000000000000000000 : ℝ)*base72 + (13433777925749/2905000000000000000000000000 : ℝ)*base74 + (2989399946871851231/290500000000000000000000000000000 : ℝ)*base76 + (985393424171851231/290500000000000000000000000000000 : ℝ)*base78 + (791639466225351231/290500000000000000000000000000000 : ℝ)*base80 + (1182371664801/726250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (31451733/2500000000000000000000 : ℝ)*base89 + (31451733/2500000000000000000000 : ℝ)*base91 + (31451733/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (129376957863815017236873/14525000000000000000000000000 : ℝ) := by norm_num
    linear_combination (232804499/20000000000000 : ℝ)*(base19) + (1040508453/100000000000000 : ℝ)*(base23) + (77315371/25000000000000 : ℝ)*(lower1) + (27557561/10000000000000 : ℝ)*(upper3) + (11894841/25000000000000 : ℝ)*(lower4) + (66035427/100000000000000 : ℝ)*(upper5) + (1298629111593361/50000000000000 : ℝ)*(major0) + (1298629111593361/50000000000000 : ℝ)*(major1) + (1298629111593361/50000000000000 : ℝ)*(major2) + (558794833/25000000000000 : ℝ)*(sp2) + (927190353564537/25000000000000 : ℝ)*(sp4) + (1854380125117827/50000000000000 : ℝ)*(sp5) + (927189534642591/25000000000000 : ℝ)*(sp6) + (297150947041779/20000000000000 : ℝ)*(sp7) + (297150947041779/20000000000000 : ℝ)*(f.failure) + (927190353564537/25000000000000 : ℝ)*(f.sum) + (814035998591/1815625000000000000000000000 : ℝ)*base65 + (9984457094242375907/1452500000000000000000000000000000 : ℝ)*base67 + (15427012006284875907/1452500000000000000000000000000000 : ℝ)*base69 + (17039278222220124093/1452500000000000000000000000000000 : ℝ)*base72 + (27113366336403/14525000000000000000000000000 : ℝ)*base73 + (45153002837245124093/1452500000000000000000000000000000 : ℝ)*base76 + (5635134051929875907/1452500000000000000000000000000000 : ℝ)*base77 + (7281407611147624093/1452500000000000000000000000000000 : ℝ)*base80 + (73267443203439/7262500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8924129/1000000000000000000000 : ℝ)*base90 + (8924129/1000000000000000000000 : ℝ)*base92 + (8924129/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1622_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16321/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10511/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (102/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1622_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1622_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3289/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (102/625 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1622_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1622_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1622_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4803/1024 : ℝ) ≤ p) (hpb : p ≤ (4807/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87405349/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3289/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (102/625 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1622_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

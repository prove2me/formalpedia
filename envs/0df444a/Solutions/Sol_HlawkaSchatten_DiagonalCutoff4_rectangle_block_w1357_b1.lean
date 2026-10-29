-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1357_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:09:52.935291+00:00
-- url     : https://prove2.me/submissions/d0afda53-eafb-4112-a634-ae99ff1cb383

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
theorem support_rectangle_w1357_s3_0 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2029470797/10000000000 : ℝ)*x 0 + (1085058463/2000000000 : ℝ)*x 1 + (654094717/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029470797/10000000000 : ℝ)^4317 ≤ (2471921788107/20000000000000 : ℝ)^3293 := by
    have hnat : (2029470797 : ℕ)^4317*20000000000000^3293 ≤ 2471921788107^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029470797 10000000000 2471921788107 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085058463/2000000000 : ℝ)^4317 ≤ (4485787126373/10000000000000 : ℝ)^3293 := by
    have hnat : (1085058463 : ℕ)^4317*10000000000000^3293 ≤ 4485787126373^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085058463 2000000000 4485787126373 10000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654094717/1250000000 : ℝ)^4317 ≤ (4278251978117/10000000000000 : ℝ)^3293 := by
    have hnat : (654094717 : ℕ)^4317*10000000000000^3293 ≤ 4278251978117^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654094717 1250000000 4278251978117 10000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2029470797/10000000000 : ℝ), (1085058463/2000000000 : ℝ), (654094717/1250000000 : ℝ)] ![(2471921788107/20000000000000 : ℝ), (4485787126373/10000000000000 : ℝ), (4278251978117/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2029470797/10000000000 : ℝ)|^4317 ≤ (2471921788107/20000000000000 : ℝ)^3293
        have hw : |(-2029470797/10000000000 : ℝ)|=(2029470797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085058463/2000000000 : ℝ)|^4317 ≤ (4485787126373/10000000000000 : ℝ)^3293
        have hw : |(1085058463/2000000000 : ℝ)|=(1085058463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654094717/1250000000 : ℝ)|^4317 ≤ (4278251978117/10000000000000 : ℝ)^3293
        have hw : |(654094717/1250000000 : ℝ)|=(654094717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s3_1 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3345093/6250000 : ℝ)*x 0 + (-2127833581/10000000000 : ℝ)*x 1 + (2616378819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3345093/6250000 : ℝ)^4317 ≤ (5508338183927/12500000000000 : ℝ)^3293 := by
    have hnat : (3345093 : ℕ)^4317*12500000000000^3293 ≤ 5508338183927^3293*6250000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3345093 6250000 5508338183927 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127833581/10000000000 : ℝ)^4317 ≤ (13150775782077/100000000000000 : ℝ)^3293 := by
    have hnat : (2127833581 : ℕ)^4317*100000000000000^3293 ≤ 13150775782077^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127833581 10000000000 13150775782077 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616378819/5000000000 : ℝ)^4317 ≤ (5347814841347/12500000000000 : ℝ)^3293 := by
    have hnat : (2616378819 : ℕ)^4317*12500000000000^3293 ≤ 5347814841347^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616378819 5000000000 5347814841347 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3345093/6250000 : ℝ), (-2127833581/10000000000 : ℝ), (2616378819/5000000000 : ℝ)] ![(5508338183927/12500000000000 : ℝ), (13150775782077/100000000000000 : ℝ), (5347814841347/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3345093/6250000 : ℝ)|^4317 ≤ (5508338183927/12500000000000 : ℝ)^3293
        have hw : |(3345093/6250000 : ℝ)|=(3345093/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2127833581/10000000000 : ℝ)|^4317 ≤ (13150775782077/100000000000000 : ℝ)^3293
        have hw : |(-2127833581/10000000000 : ℝ)|=(2127833581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616378819/5000000000 : ℝ)|^4317 ≤ (5347814841347/12500000000000 : ℝ)^3293
        have hw : |(2616378819/5000000000 : ℝ)|=(2616378819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s3_2 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070429737/2000000000 : ℝ)*x 0 + (209310313/400000000 : ℝ)*x 1 + (-2127833487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070429737/2000000000 : ℝ)^4317 ≤ (22033352115067/50000000000000 : ℝ)^3293 := by
    have hnat : (1070429737 : ℕ)^4317*50000000000000^3293 ≤ 22033352115067^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070429737 2000000000 22033352115067 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209310313/400000000 : ℝ)^4317 ≤ (42782520735099/100000000000000 : ℝ)^3293 := by
    have hnat : (209310313 : ℕ)^4317*100000000000000^3293 ≤ 42782520735099^3293*400000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209310313 400000000 42782520735099 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127833487/10000000000 : ℝ)^4317 ≤ (13150775020469/100000000000000 : ℝ)^3293 := by
    have hnat : (2127833487 : ℕ)^4317*100000000000000^3293 ≤ 13150775020469^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127833487 10000000000 13150775020469 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070429737/2000000000 : ℝ), (209310313/400000000 : ℝ), (-2127833487/10000000000 : ℝ)] ![(22033352115067/50000000000000 : ℝ), (42782520735099/100000000000000 : ℝ), (13150775020469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070429737/2000000000 : ℝ)|^4317 ≤ (22033352115067/50000000000000 : ℝ)^3293
        have hw : |(1070429737/2000000000 : ℝ)|=(1070429737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209310313/400000000 : ℝ)|^4317 ≤ (42782520735099/100000000000000 : ℝ)^3293
        have hw : |(209310313/400000000 : ℝ)|=(209310313/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2127833487/10000000000 : ℝ)|^4317 ≤ (13150775020469/100000000000000 : ℝ)^3293
        have hw : |(-2127833487/10000000000 : ℝ)|=(2127833487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s3_3 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321735193/10000000000 : ℝ)*x 0 + (2061685953/5000000000 : ℝ)*x 1 + (905785387/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321735193/10000000000 : ℝ)^4317 ≤ (33293652865773/100000000000000 : ℝ)^3293 := by
    have hnat : (4321735193 : ℕ)^4317*100000000000000^3293 ≤ 33293652865773^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321735193 10000000000 33293652865773 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061685953/5000000000 : ℝ)^4317 ≤ (31304762158589/100000000000000 : ℝ)^3293 := by
    have hnat : (2061685953 : ℕ)^4317*100000000000000^3293 ≤ 31304762158589^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061685953 5000000000 31304762158589 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905785387/2000000000 : ℝ)^4317 ≤ (17700792482809/50000000000000 : ℝ)^3293 := by
    have hnat : (905785387 : ℕ)^4317*50000000000000^3293 ≤ 17700792482809^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905785387 2000000000 17700792482809 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321735193/10000000000 : ℝ), (2061685953/5000000000 : ℝ), (905785387/2000000000 : ℝ)] ![(33293652865773/100000000000000 : ℝ), (31304762158589/100000000000000 : ℝ), (17700792482809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321735193/10000000000 : ℝ)|^4317 ≤ (33293652865773/100000000000000 : ℝ)^3293
        have hw : |(4321735193/10000000000 : ℝ)|=(4321735193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2061685953/5000000000 : ℝ)|^4317 ≤ (31304762158589/100000000000000 : ℝ)^3293
        have hw : |(2061685953/5000000000 : ℝ)|=(2061685953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(905785387/2000000000 : ℝ)|^4317 ≤ (17700792482809/50000000000000 : ℝ)^3293
        have hw : |(905785387/2000000000 : ℝ)|=(905785387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s3_4 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2029489319/10000000000 : ℝ)*x 0 + (5233553259/10000000000 : ℝ)*x 1 + (5424492001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029489319/10000000000 : ℝ)^4317 ≤ (12359756817571/100000000000000 : ℝ)^3293 := by
    have hnat : (2029489319 : ℕ)^4317*100000000000000^3293 ≤ 12359756817571^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029489319 10000000000 12359756817571 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233553259/10000000000 : ℝ)^4317 ≤ (21395523319823/50000000000000 : ℝ)^3293 := by
    have hnat : (5233553259 : ℕ)^4317*50000000000000^3293 ≤ 21395523319823^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233553259 10000000000 21395523319823 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424492001/10000000000 : ℝ)^4317 ≤ (8969839305461/20000000000000 : ℝ)^3293 := by
    have hnat : (5424492001 : ℕ)^4317*20000000000000^3293 ≤ 8969839305461^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424492001 10000000000 8969839305461 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2029489319/10000000000 : ℝ), (5233553259/10000000000 : ℝ), (5424492001/10000000000 : ℝ)] ![(12359756817571/100000000000000 : ℝ), (21395523319823/50000000000000 : ℝ), (8969839305461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2029489319/10000000000 : ℝ)|^4317 ≤ (12359756817571/100000000000000 : ℝ)^3293
        have hw : |(-2029489319/10000000000 : ℝ)|=(2029489319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233553259/10000000000 : ℝ)|^4317 ≤ (21395523319823/50000000000000 : ℝ)^3293
        have hw : |(5233553259/10000000000 : ℝ)|=(5233553259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424492001/10000000000 : ℝ)|^4317 ≤ (8969839305461/20000000000000 : ℝ)^3293
        have hw : |(5424492001/10000000000 : ℝ)|=(5424492001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s3_5 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325617607/2500000000 : ℝ)*x 0 + (-387219863/2000000000 : ℝ)*x 1 + (5424492331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325617607/2500000000 : ℝ)^4317 ≤ (10882816149577/25000000000000 : ℝ)^3293 := by
    have hnat : (1325617607 : ℕ)^4317*25000000000000^3293 ≤ 10882816149577^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325617607 2500000000 10882816149577 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387219863/2000000000 : ℝ)^4317 ≤ (1452441911243/12500000000000 : ℝ)^3293 := by
    have hnat : (387219863 : ℕ)^4317*12500000000000^3293 ≤ 1452441911243^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387219863 2000000000 1452441911243 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424492331/10000000000 : ℝ)^4317 ≤ (11212300026037/25000000000000 : ℝ)^3293 := by
    have hnat : (5424492331 : ℕ)^4317*25000000000000^3293 ≤ 11212300026037^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424492331 10000000000 11212300026037 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325617607/2500000000 : ℝ), (-387219863/2000000000 : ℝ), (5424492331/10000000000 : ℝ)] ![(10882816149577/25000000000000 : ℝ), (1452441911243/12500000000000 : ℝ), (11212300026037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325617607/2500000000 : ℝ)|^4317 ≤ (10882816149577/25000000000000 : ℝ)^3293
        have hw : |(1325617607/2500000000 : ℝ)|=(1325617607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-387219863/2000000000 : ℝ)|^4317 ≤ (1452441911243/12500000000000 : ℝ)^3293
        have hw : |(-387219863/2000000000 : ℝ)|=(387219863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424492331/10000000000 : ℝ)|^4317 ≤ (11212300026037/25000000000000 : ℝ)^3293
        have hw : |(5424492331/10000000000 : ℝ)|=(5424492331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s3_6 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165702223/312500000 : ℝ)*x 0 + (1356122963/2500000000 : ℝ)*x 1 + (-387219801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165702223/312500000 : ℝ)^4317 ≤ (43531272218161/100000000000000 : ℝ)^3293 := by
    have hnat : (165702223 : ℕ)^4317*100000000000000^3293 ≤ 43531272218161^3293*312500000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165702223 312500000 43531272218161 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356122963/2500000000 : ℝ)^4317 ≤ (22424597456153/50000000000000 : ℝ)^3293 := by
    have hnat : (1356122963 : ℕ)^4317*50000000000000^3293 ≤ 22424597456153^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356122963 2500000000 22424597456153 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387219801/2000000000 : ℝ)^4317 ≤ (1452441606367/12500000000000 : ℝ)^3293 := by
    have hnat : (387219801 : ℕ)^4317*12500000000000^3293 ≤ 1452441606367^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387219801 2000000000 1452441606367 12500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165702223/312500000 : ℝ), (1356122963/2500000000 : ℝ), (-387219801/2000000000 : ℝ)] ![(43531272218161/100000000000000 : ℝ), (22424597456153/50000000000000 : ℝ), (1452441606367/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165702223/312500000 : ℝ)|^4317 ≤ (43531272218161/100000000000000 : ℝ)^3293
        have hw : |(165702223/312500000 : ℝ)|=(165702223/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356122963/2500000000 : ℝ)|^4317 ≤ (22424597456153/50000000000000 : ℝ)^3293
        have hw : |(1356122963/2500000000 : ℝ)|=(1356122963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387219801/2000000000 : ℝ)|^4317 ≤ (1452441606367/12500000000000 : ℝ)^3293
        have hw : |(-387219801/2000000000 : ℝ)|=(387219801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s3_7 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321774901/10000000000 : ℝ)*x 0 + (4527250729/10000000000 : ℝ)*x 1 + (257816077/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321774901/10000000000 : ℝ)^4317 ≤ (3329405389151/10000000000000 : ℝ)^3293 := by
    have hnat : (4321774901 : ℕ)^4317*10000000000000^3293 ≤ 3329405389151^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321774901 10000000000 3329405389151 10000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4527250729/10000000000 : ℝ)^4317 ≤ (35384409041753/100000000000000 : ℝ)^3293 := by
    have hnat : (4527250729 : ℕ)^4317*100000000000000^3293 ≤ 35384409041753^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527250729 10000000000 35384409041753 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257816077/625000000 : ℝ)^4317 ≤ (15660768525343/50000000000000 : ℝ)^3293 := by
    have hnat : (257816077 : ℕ)^4317*50000000000000^3293 ≤ 15660768525343^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257816077 625000000 15660768525343 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321774901/10000000000 : ℝ), (4527250729/10000000000 : ℝ), (257816077/625000000 : ℝ)] ![(3329405389151/10000000000000 : ℝ), (35384409041753/100000000000000 : ℝ), (15660768525343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321774901/10000000000 : ℝ)|^4317 ≤ (3329405389151/10000000000000 : ℝ)^3293
        have hw : |(4321774901/10000000000 : ℝ)|=(4321774901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4527250729/10000000000 : ℝ)|^4317 ≤ (35384409041753/100000000000000 : ℝ)^3293
        have hw : |(4527250729/10000000000 : ℝ)|=(4527250729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(257816077/625000000 : ℝ)|^4317 ≤ (15660768525343/50000000000000 : ℝ)^3293
        have hw : |(257816077/625000000 : ℝ)|=(257816077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1357_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2487/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10921/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3749/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2487/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2487/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2487/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2487/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2487/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2487/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2487/25000 : ℝ) ^ (1079/256 : ℝ) ≤ (5965033707493977/100000000000000000000 : ℝ) := by
    have hpowers : (2487/25000 : ℝ)^1079 ≤ (5965033707493977/100000000000000000000 : ℝ)^256 := by
      have hnat : (2487 : ℕ)^1079*100000000000000000000^256 ≤ 5965033707493977^256*25000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2487 25000 5965033707493977 100000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2487/25000 : ℝ)) (X := (5965033707493977/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hpowhi : (8023/50000 : ℝ) ^ (1079/256 : ℝ) ≤ (44745067986821767/100000000000000000000 : ℝ) := by
    have hpowers : (8023/50000 : ℝ)^1079 ≤ (44745067986821767/100000000000000000000 : ℝ)^256 := by
      have hnat : (8023 : ℕ)^1079*100000000000000000000^256 ≤ 44745067986821767^256*50000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8023 50000 44745067986821767 100000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8023/50000 : ℝ)) (X := (44745067986821767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005965033707493977/50000000000000000000 : ℝ) ≤ (10000283035988229/10000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50005965033707493977/50000000000000000000 : ℝ)^256 ≤ (10000283035988229/10000000000000000 : ℝ)^1079 := by
      have hnat : (50005965033707493977 : ℕ)^256*10000000000000000^1079 ≤ 10000283035988229^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005965033707493977 50000000000000000000 10000283035988229 10000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283035988229/10000000000000000 : ℝ)) (X := (50005965033707493977/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126584690677947367/3125000000000000000 : ℝ) ≤ (5000601449313379/5000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (3126584690677947367/3125000000000000000 : ℝ)^256 ≤ (5000601449313379/5000000000000000 : ℝ)^1079 := by
      have hnat : (3126584690677947367 : ℕ)^256*5000000000000000^1079 ≤ 5000601449313379^1079*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126584690677947367 3125000000000000000 5000601449313379 5000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000601449313379/5000000000000000 : ℝ)) (X := (3126584690677947367/3125000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50044745067986821767/50000000000000000000 : ℝ) ≤ (10002122761265287/10000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50044745067986821767/50000000000000000000 : ℝ)^256 ≤ (10002122761265287/10000000000000000 : ℝ)^1079 := by
      have hnat : (50044745067986821767 : ℕ)^256*10000000000000000^1079 ≤ 10002122761265287^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044745067986821767 50000000000000000000 10002122761265287 10000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002122761265287/10000000000000000 : ℝ)) (X := (50044745067986821767/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5965033707493977/100000000000000000000 : ℝ) ≤ ((30481712183200023729/30490000000000000000 : ℝ)+2*(919862638529/609800000000000 : ℝ)*(2487/25000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (30481712183200023729/30490000000000000000 : ℝ)+2*(919862638529/609800000000000 : ℝ)*(2487/25000 : ℝ)=(10000283035988229/10000000000000000 : ℝ) by norm_num, show 1+2*(5965033707493977/100000000000000000000 : ℝ)=(50005965033707493977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44745067986821767/100000000000000000000 : ℝ)+(5965033707493977/100000000000000000000 : ℝ) ≤ ((30481712183200023729/30490000000000000000 : ℝ)+(919862638529/609800000000000 : ℝ)*((8023/50000 : ℝ)+(2487/25000 : ℝ)))^(1079/256 : ℝ) := by
    rw [show (30481712183200023729/30490000000000000000 : ℝ)+(919862638529/609800000000000 : ℝ)*((8023/50000 : ℝ)+(2487/25000 : ℝ))=(5000601449313379/5000000000000000 : ℝ) by norm_num, show 1+(44745067986821767/100000000000000000000 : ℝ)+(5965033707493977/100000000000000000000 : ℝ)=(3126584690677947367/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44745067986821767/100000000000000000000 : ℝ) ≤ ((30481712183200023729/30490000000000000000 : ℝ)+2*(919862638529/609800000000000 : ℝ)*(8023/50000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (30481712183200023729/30490000000000000000 : ℝ)+2*(919862638529/609800000000000 : ℝ)*(8023/50000 : ℝ)=(10002122761265287/10000000000000000 : ℝ) by norm_num, show 1+2*(44745067986821767/100000000000000000000 : ℝ)=(50044745067986821767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30481712183200023729/30490000000000000000 : ℝ)*(X 1 0+X 2 0)+(919862638529/609800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (2487/25000 : ℝ)) (hi := (8023/50000 : ℝ)) (c := (30481712183200023729/30490000000000000000 : ℝ)) (alpha := (919862638529/609800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30481712183200023729/30490000000000000000 : ℝ)*(X 0 1+X 2 1)+(919862638529/609800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (2487/25000 : ℝ)) (hi := (8023/50000 : ℝ)) (c := (30481712183200023729/30490000000000000000 : ℝ)) (alpha := (919862638529/609800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30481712183200023729/30490000000000000000 : ℝ)*(X 0 2+X 1 2)+(919862638529/609800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (2487/25000 : ℝ)) (hi := (8023/50000 : ℝ)) (c := (30481712183200023729/30490000000000000000 : ℝ)) (alpha := (919862638529/609800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2029470797/10000000000 : ℝ)*X 0 0+(1085058463/2000000000 : ℝ)*X 0 1+(654094717/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((3345093/6250000 : ℝ)*X 1 0+(-2127833581/10000000000 : ℝ)*X 1 1+(2616378819/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070429737/2000000000 : ℝ)*X 2 0+(209310313/400000000 : ℝ)*X 2 1+(-2127833487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321735193/10000000000 : ℝ)*X 0 0+(2061685953/5000000000 : ℝ)*X 0 1+(905785387/2000000000 : ℝ)*X 0 2+(4321735193/10000000000 : ℝ)*X 1 0+(2061685953/5000000000 : ℝ)*X 1 1+(905785387/2000000000 : ℝ)*X 1 2+(4321735193/10000000000 : ℝ)*X 2 0+(2061685953/5000000000 : ℝ)*X 2 1+(905785387/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2029489319/10000000000 : ℝ)*X 0 0+(5233553259/10000000000 : ℝ)*X 0 1+(5424492001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325617607/2500000000 : ℝ)*X 1 0+(-387219863/2000000000 : ℝ)*X 1 1+(5424492331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165702223/312500000 : ℝ)*X 2 0+(1356122963/2500000000 : ℝ)*X 2 1+(-387219801/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321774901/10000000000 : ℝ)*X 0 0+(4527250729/10000000000 : ℝ)*X 0 1+(257816077/625000000 : ℝ)*X 0 2+(4321774901/10000000000 : ℝ)*X 1 0+(4527250729/10000000000 : ℝ)*X 1 1+(257816077/625000000 : ℝ)*X 1 2+(4321774901/10000000000 : ℝ)*X 2 0+(4527250729/10000000000 : ℝ)*X 2 1+(257816077/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1844111307274280647929969/297753906250000000000000000000 : ℝ) := by norm_num
    linear_combination (56517079/4000000000000 : ℝ)*(base19) + (1289746921/100000000000000 : ℝ)*(base23) + (6197669/100000000000000 : ℝ)*(lower2) + (18151433/20000000000000 : ℝ)*(upper3) + (164169077/100000000000000 : ℝ)*(upper5) + (47873185338359/1250000000000 : ℝ)*(major0) + (47873185338359/1250000000000 : ℝ)*(major1) + (47873185338359/1250000000000 : ℝ)*(major2) + (2596948953867463/50000000000000 : ℝ)*(sp0) + (2596962118656881/50000000000000 : ℝ)*(sp1) + (649240545061727/12500000000000 : ℝ)*(sp2) + (1232885392067649/50000000000000 : ℝ)*(sp3) + (27742505811/100000000000000 : ℝ)*(sp4) + (162666431/1250000000000 : ℝ)*(sp7) + (2465783797449777/100000000000000 : ℝ)*(f.failure) + (5193925650240737/100000000000000 : ℝ)*(f.sum) + (3168603589401/3049000000000000000000000000 : ℝ)*base65 + (58214073956816789/38112500000000000000000000000000 : ℝ)*base68 + (240811087754441789/38112500000000000000000000000000 : ℝ)*base70 + (311312286074354289/38112500000000000000000000000000 : ℝ)*base72 + (6152889271913/1524500000000000000000000000 : ℝ)*base74 + (430558315987454289/38112500000000000000000000000000 : ℝ)*base76 + (193935737030145711/38112500000000000000000000000000 : ℝ)*base77 + (190377874926679289/38112500000000000000000000000000 : ℝ)*base80 + (5732435849007/1524500000000000000000000000 : ℝ)*base82 + (22295129/10000000000000000000000 : ℝ)*base89 + (22295129/10000000000000000000000 : ℝ)*base91 + (22295129/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1062510441512837430069859137/152450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (733937293/50000000000000 : ℝ)*(base19) + (1344276173/50000000000000 : ℝ)*(base23) + (294721519/100000000000000 : ℝ)*(upper3) + (183522253/100000000000000 : ℝ)*(lower4) + (25977701/10000000000000 : ℝ)*(upper5) + (386182507982149/10000000000000 : ℝ)*(major0) + (386182507982149/10000000000000 : ℝ)*(major1) + (386182507982149/10000000000000 : ℝ)*(major2) + (1791981223/6250000000000 : ℝ)*(sp1) + (23690322783/50000000000000 : ℝ)*(sp2) + (654660331527959/12500000000000 : ℝ)*(sp4) + (2618626256324759/50000000000000 : ℝ)*(sp5) + (32732703643911/625000000000 : ℝ)*(sp6) + (1243183637550207/50000000000000 : ℝ)*(sp7) + (1243183637550207/50000000000000 : ℝ)*(f.failure) + (654660331527959/12500000000000 : ℝ)*(f.sum) + (7598367851833/3049000000000000000000000000 : ℝ)*base66 + (116215594064863621/304900000000000000000000000000000 : ℝ)*base67 + (288476000778536379/304900000000000000000000000000000 : ℝ)*base70 + (786924776771263621/304900000000000000000000000000000 : ℝ)*base71 + (6086914467951/3049000000000000000000000000 : ℝ)*base74 + (885907582288463621/304900000000000000000000000000000 : ℝ)*base75 + (587342445662136379/304900000000000000000000000000000 : ℝ)*base78 + (4545920356797063621/304900000000000000000000000000000 : ℝ)*base79 + (10995327627127/3049000000000000000000000000 : ℝ)*base81 + (12414761/5000000000000000000000 : ℝ)*base90 + (12414761/5000000000000000000000 : ℝ)*base92 + (12414761/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1357_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2487/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10921/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3749/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1357_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1357_s4_0 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1015407413/5000000000 : ℝ)*x 0 + (5414235757/10000000000 : ℝ)*x 1 + (2621465683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1015407413/5000000000 : ℝ)^4317 ≤ (12370340568053/100000000000000 : ℝ)^3293 := by
    have hnat : (1015407413 : ℕ)^4317*100000000000000^3293 ≤ 12370340568053^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015407413 5000000000 12370340568053 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414235757/10000000000 : ℝ)^4317 ≤ (44738062638601/100000000000000 : ℝ)^3293 := by
    have hnat : (5414235757 : ℕ)^4317*100000000000000^3293 ≤ 44738062638601^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414235757 10000000000 44738062638601 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621465683/5000000000 : ℝ)^4317 ≤ (42891596783147/100000000000000 : ℝ)^3293 := by
    have hnat : (2621465683 : ℕ)^4317*100000000000000^3293 ≤ 42891596783147^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621465683 5000000000 42891596783147 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1015407413/5000000000 : ℝ), (5414235757/10000000000 : ℝ), (2621465683/5000000000 : ℝ)] ![(12370340568053/100000000000000 : ℝ), (44738062638601/100000000000000 : ℝ), (42891596783147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1015407413/5000000000 : ℝ)|^4317 ≤ (12370340568053/100000000000000 : ℝ)^3293
        have hw : |(-1015407413/5000000000 : ℝ)|=(1015407413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414235757/10000000000 : ℝ)|^4317 ≤ (44738062638601/100000000000000 : ℝ)^3293
        have hw : |(5414235757/10000000000 : ℝ)|=(5414235757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621465683/5000000000 : ℝ)|^4317 ≤ (42891596783147/100000000000000 : ℝ)^3293
        have hw : |(2621465683/5000000000 : ℝ)|=(2621465683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s4_1 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069864889/2000000000 : ℝ)*x 0 + (-1059063223/5000000000 : ℝ)*x 1 + (1310732803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069864889/2000000000 : ℝ)^4317 ≤ (11009055641367/25000000000000 : ℝ)^3293 := by
    have hnat : (1069864889 : ℕ)^4317*25000000000000^3293 ≤ 11009055641367^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069864889 2000000000 11009055641367 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059063223/5000000000 : ℝ)^4317 ≤ (13072182283287/100000000000000 : ℝ)^3293 := by
    have hnat : (1059063223 : ℕ)^4317*100000000000000^3293 ≤ 13072182283287^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059063223 5000000000 13072182283287 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310732803/2500000000 : ℝ)^4317 ≤ (42891595131531/100000000000000 : ℝ)^3293 := by
    have hnat : (1310732803 : ℕ)^4317*100000000000000^3293 ≤ 42891595131531^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310732803 2500000000 42891595131531 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069864889/2000000000 : ℝ), (-1059063223/5000000000 : ℝ), (1310732803/2500000000 : ℝ)] ![(11009055641367/25000000000000 : ℝ), (13072182283287/100000000000000 : ℝ), (42891595131531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069864889/2000000000 : ℝ)|^4317 ≤ (11009055641367/25000000000000 : ℝ)^3293
        have hw : |(1069864889/2000000000 : ℝ)|=(1069864889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1059063223/5000000000 : ℝ)|^4317 ≤ (13072182283287/100000000000000 : ℝ)^3293
        have hw : |(-1059063223/5000000000 : ℝ)|=(1059063223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310732803/2500000000 : ℝ)|^4317 ≤ (42891595131531/100000000000000 : ℝ)^3293
        have hw : |(1310732803/2500000000 : ℝ)|=(1310732803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s4_2 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337331101/2500000000 : ℝ)*x 0 + (5242931419/10000000000 : ℝ)*x 1 + (-2118126227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337331101/2500000000 : ℝ)^4317 ≤ (44036222122997/100000000000000 : ℝ)^3293 := by
    have hnat : (1337331101 : ℕ)^4317*100000000000000^3293 ≤ 44036222122997^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337331101 2500000000 44036222122997 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242931419/10000000000 : ℝ)^4317 ≤ (1072289933789/2500000000000 : ℝ)^3293 := by
    have hnat : (5242931419 : ℕ)^4317*2500000000000^3293 ≤ 1072289933789^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242931419 10000000000 1072289933789 2500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118126227/10000000000 : ℝ)^4317 ≤ (13072180511421/100000000000000 : ℝ)^3293 := by
    have hnat : (2118126227 : ℕ)^4317*100000000000000^3293 ≤ 13072180511421^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118126227 10000000000 13072180511421 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337331101/2500000000 : ℝ), (5242931419/10000000000 : ℝ), (-2118126227/10000000000 : ℝ)] ![(44036222122997/100000000000000 : ℝ), (1072289933789/2500000000000 : ℝ), (13072180511421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337331101/2500000000 : ℝ)|^4317 ≤ (44036222122997/100000000000000 : ℝ)^3293
        have hw : |(1337331101/2500000000 : ℝ)|=(1337331101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242931419/10000000000 : ℝ)|^4317 ≤ (1072289933789/2500000000000 : ℝ)^3293
        have hw : |(5242931419/10000000000 : ℝ)|=(5242931419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2118126227/10000000000 : ℝ)|^4317 ≤ (13072180511421/100000000000000 : ℝ)^3293
        have hw : |(-2118126227/10000000000 : ℝ)|=(2118126227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s4_3 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322553149/10000000000 : ℝ)*x 0 + (4145630979/10000000000 : ℝ)*x 1 + (2253233109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322553149/10000000000 : ℝ)^4317 ≤ (33301913936381/100000000000000 : ℝ)^3293 := by
    have hnat : (4322553149 : ℕ)^4317*100000000000000^3293 ≤ 33301913936381^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322553149 10000000000 33301913936381 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145630979/10000000000 : ℝ)^4317 ≤ (7881622369379/25000000000000 : ℝ)^3293 := by
    have hnat : (4145630979 : ℕ)^4317*25000000000000^3293 ≤ 7881622369379^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145630979 10000000000 7881622369379 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253233109/5000000000 : ℝ)^4317 ≤ (35171596565141/100000000000000 : ℝ)^3293 := by
    have hnat : (2253233109 : ℕ)^4317*100000000000000^3293 ≤ 35171596565141^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253233109 5000000000 35171596565141 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322553149/10000000000 : ℝ), (4145630979/10000000000 : ℝ), (2253233109/5000000000 : ℝ)] ![(33301913936381/100000000000000 : ℝ), (7881622369379/25000000000000 : ℝ), (35171596565141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322553149/10000000000 : ℝ)|^4317 ≤ (33301913936381/100000000000000 : ℝ)^3293
        have hw : |(4322553149/10000000000 : ℝ)|=(4322553149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4145630979/10000000000 : ℝ)|^4317 ≤ (7881622369379/25000000000000 : ℝ)^3293
        have hw : |(4145630979/10000000000 : ℝ)|=(4145630979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253233109/5000000000 : ℝ)|^4317 ≤ (35171596565141/100000000000000 : ℝ)^3293
        have hw : |(2253233109/5000000000 : ℝ)|=(2253233109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s4_4 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1015413881/5000000000 : ℝ)*x 0 + (209742463/400000000 : ℝ)*x 1 + (5413602257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1015413881/5000000000 : ℝ)^4317 ≤ (12370443868473/100000000000000 : ℝ)^3293 := by
    have hnat : (1015413881 : ℕ)^4317*100000000000000^3293 ≤ 12370443868473^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015413881 5000000000 12370443868473 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209742463/400000000 : ℝ)^4317 ≤ (42898355761839/100000000000000 : ℝ)^3293 := by
    have hnat : (209742463 : ℕ)^4317*100000000000000^3293 ≤ 42898355761839^3293*400000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209742463 400000000 42898355761839 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413602257/10000000000 : ℝ)^4317 ≤ (44731200348929/100000000000000 : ℝ)^3293 := by
    have hnat : (5413602257 : ℕ)^4317*100000000000000^3293 ≤ 44731200348929^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413602257 10000000000 44731200348929 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1015413881/5000000000 : ℝ), (209742463/400000000 : ℝ), (5413602257/10000000000 : ℝ)] ![(12370443868473/100000000000000 : ℝ), (42898355761839/100000000000000 : ℝ), (44731200348929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1015413881/5000000000 : ℝ)|^4317 ≤ (12370443868473/100000000000000 : ℝ)^3293
        have hw : |(-1015413881/5000000000 : ℝ)|=(1015413881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209742463/400000000 : ℝ)|^4317 ≤ (42898355761839/100000000000000 : ℝ)^3293
        have hw : |(209742463/400000000 : ℝ)|=(209742463/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413602257/10000000000 : ℝ)|^4317 ≤ (44731200348929/100000000000000 : ℝ)^3293
        have hw : |(5413602257/10000000000 : ℝ)|=(5413602257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s4_5 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305125167/10000000000 : ℝ)*x 0 + (-389491049/2000000000 : ℝ)*x 1 + (2706801069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305125167/10000000000 : ℝ)^4317 ≤ (21779919231317/50000000000000 : ℝ)^3293 := by
    have hnat : (5305125167 : ℕ)^4317*50000000000000^3293 ≤ 21779919231317^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305125167 10000000000 21779919231317 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389491049/2000000000 : ℝ)^4317 ≤ (5854481231009/50000000000000 : ℝ)^3293 := by
    have hnat : (389491049 : ℕ)^4317*50000000000000^3293 ≤ 5854481231009^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389491049 2000000000 5854481231009 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706801069/5000000000 : ℝ)^4317 ≤ (698924985311/1562500000000 : ℝ)^3293 := by
    have hnat : (2706801069 : ℕ)^4317*1562500000000^3293 ≤ 698924985311^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706801069 5000000000 698924985311 1562500000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305125167/10000000000 : ℝ), (-389491049/2000000000 : ℝ), (2706801069/5000000000 : ℝ)] ![(21779919231317/50000000000000 : ℝ), (5854481231009/50000000000000 : ℝ), (698924985311/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305125167/10000000000 : ℝ)|^4317 ≤ (21779919231317/50000000000000 : ℝ)^3293
        have hw : |(5305125167/10000000000 : ℝ)|=(5305125167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389491049/2000000000 : ℝ)|^4317 ≤ (5854481231009/50000000000000 : ℝ)^3293
        have hw : |(-389491049/2000000000 : ℝ)|=(389491049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706801069/5000000000 : ℝ)|^4317 ≤ (698924985311/1562500000000 : ℝ)^3293
        have hw : |(2706801069/5000000000 : ℝ)|=(2706801069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s4_6 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652562417/5000000000 : ℝ)*x 0 + (5286721/9765625 : ℝ)*x 1 + (-121715967/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652562417/5000000000 : ℝ)^4317 ≤ (21779917439081/50000000000000 : ℝ)^3293 := by
    have hnat : (2652562417 : ℕ)^4317*50000000000000^3293 ≤ 21779917439081^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652562417 5000000000 21779917439081 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5286721/9765625 : ℝ)^4317 ≤ (1118280021451/2500000000000 : ℝ)^3293 := by
    have hnat : (5286721 : ℕ)^4317*2500000000000^3293 ≤ 1118280021451^3293*9765625^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286721 9765625 1118280021451 2500000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121715967/625000000 : ℝ)^4317 ≤ (2927241062813/25000000000000 : ℝ)^3293 := by
    have hnat : (121715967 : ℕ)^4317*25000000000000^3293 ≤ 2927241062813^3293*625000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121715967 625000000 2927241062813 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652562417/5000000000 : ℝ), (5286721/9765625 : ℝ), (-121715967/625000000 : ℝ)] ![(21779917439081/50000000000000 : ℝ), (1118280021451/2500000000000 : ℝ), (2927241062813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652562417/5000000000 : ℝ)|^4317 ≤ (21779917439081/50000000000000 : ℝ)^3293
        have hw : |(2652562417/5000000000 : ℝ)|=(2652562417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5286721/9765625 : ℝ)|^4317 ≤ (1118280021451/2500000000000 : ℝ)^3293
        have hw : |(5286721/9765625 : ℝ)|=(5286721/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121715967/625000000 : ℝ)|^4317 ≤ (2927241062813/25000000000000 : ℝ)^3293
        have hw : |(-121715967/625000000 : ℝ)|=(121715967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s4_7 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322580239/10000000000 : ℝ)*x 0 + (7039279/15625000 : ℝ)*x 1 + (1036741493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322580239/10000000000 : ℝ)^4317 ≤ (33302187544259/100000000000000 : ℝ)^3293 := by
    have hnat : (4322580239 : ℕ)^4317*100000000000000^3293 ≤ 33302187544259^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322580239 10000000000 33302187544259 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7039279/15625000 : ℝ)^4317 ≤ (35158013036511/100000000000000 : ℝ)^3293 := by
    have hnat : (7039279 : ℕ)^4317*100000000000000^3293 ≤ 35158013036511^3293*15625000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7039279 15625000 35158013036511 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036741493/2500000000 : ℝ)^4317 ≤ (15769899707597/50000000000000 : ℝ)^3293 := by
    have hnat : (1036741493 : ℕ)^4317*50000000000000^3293 ≤ 15769899707597^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036741493 2500000000 15769899707597 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322580239/10000000000 : ℝ), (7039279/15625000 : ℝ), (1036741493/2500000000 : ℝ)] ![(33302187544259/100000000000000 : ℝ), (35158013036511/100000000000000 : ℝ), (15769899707597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322580239/10000000000 : ℝ)|^4317 ≤ (33302187544259/100000000000000 : ℝ)^3293
        have hw : |(4322580239/10000000000 : ℝ)|=(4322580239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7039279/15625000 : ℝ)|^4317 ≤ (35158013036511/100000000000000 : ℝ)^3293
        have hw : |(7039279/15625000 : ℝ)|=(7039279/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036741493/2500000000 : ℝ)|^4317 ≤ (15769899707597/50000000000000 : ℝ)^3293
        have hw : |(1036741493/2500000000 : ℝ)|=(1036741493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1357_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3749/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5569/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2953/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3749/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10921/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3749/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10921/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3749/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10921/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3749/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10921/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3749/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10921/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3749/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10921/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10921/100000 : ℝ) ^ (1079/256 : ℝ) ≤ (8839471856875161/100000000000000000000 : ℝ) := by
    have hpowers : (10921/100000 : ℝ)^1079 ≤ (8839471856875161/100000000000000000000 : ℝ)^256 := by
      have hnat : (10921 : ℕ)^1079*100000000000000000000^256 ≤ 8839471856875161^256*100000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10921 100000 8839471856875161 100000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10921/100000 : ℝ)) (X := (8839471856875161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3749/25000 : ℝ) ^ (1079/256 : ℝ) ≤ (16820356761837509/50000000000000000000 : ℝ) := by
    have hpowers : (3749/25000 : ℝ)^1079 ≤ (16820356761837509/50000000000000000000 : ℝ)^256 := by
      have hnat : (3749 : ℕ)^1079*50000000000000000000^256 ≤ 16820356761837509^256*25000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3749 25000 16820356761837509 50000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3749/25000 : ℝ)) (X := (16820356761837509/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008839471856875161/50000000000000000000 : ℝ) ≤ (5000209708270673/5000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50008839471856875161/50000000000000000000 : ℝ)^256 ≤ (5000209708270673/5000000000000000 : ℝ)^1079 := by
      have hnat : (50008839471856875161 : ℕ)^256*5000000000000000^1079 ≤ 5000209708270673^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008839471856875161 50000000000000000000 5000209708270673 5000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000209708270673/5000000000000000 : ℝ)) (X := (50008839471856875161/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042480185380550179/100000000000000000000 : ℝ) ≤ (2500251926924897/2500000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (100042480185380550179/100000000000000000000 : ℝ)^256 ≤ (2500251926924897/2500000000000000 : ℝ)^1079 := by
      have hnat : (100042480185380550179 : ℕ)^256*2500000000000000^1079 ≤ 2500251926924897^1079*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042480185380550179 100000000000000000000 2500251926924897 2500000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500251926924897/2500000000000000 : ℝ)) (X := (100042480185380550179/100000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016820356761837509/25000000000000000000 : ℝ) ≤ (1000159599885783/1000000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (25016820356761837509/25000000000000000000 : ℝ)^256 ≤ (1000159599885783/1000000000000000 : ℝ)^1079 := by
      have hnat : (25016820356761837509 : ℕ)^256*1000000000000000^1079 ≤ 1000159599885783^1079*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016820356761837509 25000000000000000000 1000159599885783 1000000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000159599885783/1000000000000000 : ℝ)) (X := (25016820356761837509/25000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8839471856875161/100000000000000000000 : ℝ) ≤ ((124965827199164611/125000000000000000 : ℝ)+2*(294145579121/203750000000000 : ℝ)*(10921/100000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (124965827199164611/125000000000000000 : ℝ)+2*(294145579121/203750000000000 : ℝ)*(10921/100000 : ℝ)=(5000209708270673/5000000000000000 : ℝ) by norm_num, show 1+2*(8839471856875161/100000000000000000000 : ℝ)=(50008839471856875161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16820356761837509/50000000000000000000 : ℝ)+(8839471856875161/100000000000000000000 : ℝ) ≤ ((124965827199164611/125000000000000000 : ℝ)+(294145579121/203750000000000 : ℝ)*((3749/25000 : ℝ)+(10921/100000 : ℝ)))^(1079/256 : ℝ) := by
    rw [show (124965827199164611/125000000000000000 : ℝ)+(294145579121/203750000000000 : ℝ)*((3749/25000 : ℝ)+(10921/100000 : ℝ))=(2500251926924897/2500000000000000 : ℝ) by norm_num, show 1+(16820356761837509/50000000000000000000 : ℝ)+(8839471856875161/100000000000000000000 : ℝ)=(100042480185380550179/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16820356761837509/50000000000000000000 : ℝ) ≤ ((124965827199164611/125000000000000000 : ℝ)+2*(294145579121/203750000000000 : ℝ)*(3749/25000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (124965827199164611/125000000000000000 : ℝ)+2*(294145579121/203750000000000 : ℝ)*(3749/25000 : ℝ)=(1000159599885783/1000000000000000 : ℝ) by norm_num, show 1+2*(16820356761837509/50000000000000000000 : ℝ)=(25016820356761837509/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (124965827199164611/125000000000000000 : ℝ)*(X 1 0+X 2 0)+(294145579121/203750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (10921/100000 : ℝ)) (hi := (3749/25000 : ℝ)) (c := (124965827199164611/125000000000000000 : ℝ)) (alpha := (294145579121/203750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (124965827199164611/125000000000000000 : ℝ)*(X 0 1+X 2 1)+(294145579121/203750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (10921/100000 : ℝ)) (hi := (3749/25000 : ℝ)) (c := (124965827199164611/125000000000000000 : ℝ)) (alpha := (294145579121/203750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (124965827199164611/125000000000000000 : ℝ)*(X 0 2+X 1 2)+(294145579121/203750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (10921/100000 : ℝ)) (hi := (3749/25000 : ℝ)) (c := (124965827199164611/125000000000000000 : ℝ)) (alpha := (294145579121/203750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1015407413/5000000000 : ℝ)*X 0 0+(5414235757/10000000000 : ℝ)*X 0 1+(2621465683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069864889/2000000000 : ℝ)*X 1 0+(-1059063223/5000000000 : ℝ)*X 1 1+(1310732803/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337331101/2500000000 : ℝ)*X 2 0+(5242931419/10000000000 : ℝ)*X 2 1+(-2118126227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322553149/10000000000 : ℝ)*X 0 0+(4145630979/10000000000 : ℝ)*X 0 1+(2253233109/5000000000 : ℝ)*X 0 2+(4322553149/10000000000 : ℝ)*X 1 0+(4145630979/10000000000 : ℝ)*X 1 1+(2253233109/5000000000 : ℝ)*X 1 2+(4322553149/10000000000 : ℝ)*X 2 0+(4145630979/10000000000 : ℝ)*X 2 1+(2253233109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1015413881/5000000000 : ℝ)*X 0 0+(209742463/400000000 : ℝ)*X 0 1+(5413602257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305125167/10000000000 : ℝ)*X 1 0+(-389491049/2000000000 : ℝ)*X 1 1+(2706801069/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652562417/5000000000 : ℝ)*X 2 0+(5286721/9765625 : ℝ)*X 2 1+(-121715967/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322580239/10000000000 : ℝ)*X 0 0+(7039279/15625000 : ℝ)*X 0 1+(1036741493/2500000000 : ℝ)*X 0 2+(4322580239/10000000000 : ℝ)*X 1 0+(7039279/15625000 : ℝ)*X 1 1+(1036741493/2500000000 : ℝ)*X 1 2+(4322580239/10000000000 : ℝ)*X 2 0+(7039279/15625000 : ℝ)*X 2 1+(1036741493/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2329046426356127066840922897/254687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (342907261/20000000000000 : ℝ)*(base19) + (320316961/20000000000000 : ℝ)*(base23) + (9121783/25000000000000 : ℝ)*(lower2) + (11380887/25000000000000 : ℝ)*(upper3) + (251409751/100000000000000 : ℝ)*(upper5) + (2152253404441857/50000000000000 : ℝ)*(major0) + (2152253404441857/50000000000000 : ℝ)*(major1) + (2152253404441857/50000000000000 : ℝ)*(major2) + (145939835983159/2500000000000 : ℝ)*(sp0) + (5837631578898211/100000000000000 : ℝ)*(sp1) + (5837631691849711/100000000000000 : ℝ)*(sp2) + (554273068736767/20000000000000 : ℝ)*(sp3) + (9963527039/25000000000000 : ℝ)*(sp4) + (7337912499/50000000000000 : ℝ)*(sp7) + (86605625609651/3125000000000 : ℝ)*(f.failure) + (1459408323358629/25000000000000 : ℝ)*(f.sum) + (8213496193587/20375000000000000000000000000 : ℝ)*base66 + (2853637880734138201/1018750000000000000000000000000000 : ℝ)*base67 + (7431521911759611799/1018750000000000000000000000000000 : ℝ)*base70 + (2904859339977888201/1018750000000000000000000000000000 : ℝ)*base71 + (30166306323837/20375000000000000000000000000 : ℝ)*base74 + (6602221972990388201/1018750000000000000000000000000000 : ℝ)*base75 + (2208462878184138201/1018750000000000000000000000000000 : ℝ)*base77 + (7919260510065388201/1018750000000000000000000000000000 : ℝ)*base79 + (120297654492587/20375000000000000000000000000 : ℝ)*base82 + (1951973/312500000000000000000 : ℝ)*base90 + (1951973/312500000000000000000 : ℝ)*base92 + (1951973/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18797520534214073284227/2037500000000000000000000000 : ℝ) := by norm_num
    linear_combination (90349497/5000000000000 : ℝ)*(base19) + (665384857/50000000000000 : ℝ)*(base23) + (7357443/100000000000000 : ℝ)*(upper2) + (173392779/100000000000000 : ℝ)*(upper5) + (433644969826823/10000000000000 : ℝ)*(major0) + (433644969826823/10000000000000 : ℝ)*(major1) + (433644969826823/10000000000000 : ℝ)*(major2) + (2432425393/100000000000000 : ℝ)*(sp0) + (732667773/1562500000000 : ℝ)*(sp1) + (3237387557/10000000000000 : ℝ)*(sp2) + (5880950776842837/100000000000000 : ℝ)*(sp4) + (5880904511540817/100000000000000 : ℝ)*(sp5) + (2940459752311473/50000000000000 : ℝ)*(sp6) + (2791945879742327/100000000000000 : ℝ)*(sp7) + (2791945879742327/100000000000000 : ℝ)*(f.failure) + (588095320926823/10000000000000 : ℝ)*(f.sum) + (3233596380757/4075000000000000000000000000 : ℝ)*base65 + (84265767444519039/203750000000000000000000000000000 : ℝ)*base67 + (1812475968661730961/203750000000000000000000000000000 : ℝ)*base70 + (342615523734519039/203750000000000000000000000000000 : ℝ)*base71 + (5357279770107/4075000000000000000000000000 : ℝ)*base73 + (1427111773002019039/203750000000000000000000000000000 : ℝ)*base75 + (478437229634230961/203750000000000000000000000000000 : ℝ)*base78 + (2145540743797980961/203750000000000000000000000000000 : ℝ)*base80 + (3462084581659/2037500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4433521/10000000000000000000000 : ℝ)*base90 + (4433521/10000000000000000000000 : ℝ)*base92 + (4433521/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1357_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3749/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1357_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1357_s5_0 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-406208323/2000000000 : ℝ)*x 0 + (5412274857/10000000000 : ℝ)*x 1 + (2622371447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406208323/2000000000 : ℝ)^4317 ≤ (6186075810559/50000000000000 : ℝ)^3293 := by
    have hnat : (406208323 : ℕ)^4317*50000000000000^3293 ≤ 6186075810559^3293*2000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406208323 2000000000 6186075810559 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412274857/10000000000 : ℝ)^4317 ≤ (4471682230583/10000000000000 : ℝ)^3293 := by
    have hnat : (5412274857 : ℕ)^4317*10000000000000^3293 ≤ 4471682230583^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412274857 10000000000 4471682230583 10000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622371447/5000000000 : ℝ)^4317 ≤ (42911026064607/100000000000000 : ℝ)^3293 := by
    have hnat : (2622371447 : ℕ)^4317*100000000000000^3293 ≤ 42911026064607^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622371447 5000000000 42911026064607 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-406208323/2000000000 : ℝ), (5412274857/10000000000 : ℝ), (2622371447/5000000000 : ℝ)] ![(6186075810559/50000000000000 : ℝ), (4471682230583/10000000000000 : ℝ), (42911026064607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-406208323/2000000000 : ℝ)|^4317 ≤ (6186075810559/50000000000000 : ℝ)^3293
        have hw : |(-406208323/2000000000 : ℝ)|=(406208323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412274857/10000000000 : ℝ)|^4317 ≤ (4471682230583/10000000000000 : ℝ)^3293
        have hw : |(5412274857/10000000000 : ℝ)|=(5412274857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622371447/5000000000 : ℝ)|^4317 ≤ (42911026064607/100000000000000 : ℝ)^3293
        have hw : |(2622371447/5000000000 : ℝ)|=(2622371447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s5_1 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348822043/10000000000 : ℝ)*x 0 + (-529098669/2500000000 : ℝ)*x 1 + (5244742929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348822043/10000000000 : ℝ)^4317 ≤ (22015400364251/50000000000000 : ℝ)^3293 := by
    have hnat : (5348822043 : ℕ)^4317*50000000000000^3293 ≤ 22015400364251^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348822043 10000000000 22015400364251 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529098669/2500000000 : ℝ)^4317 ≤ (52232691277/400000000000 : ℝ)^3293 := by
    have hnat : (529098669 : ℕ)^4317*400000000000^3293 ≤ 52232691277^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529098669 2500000000 52232691277 400000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244742929/10000000000 : ℝ)^4317 ≤ (8582205288003/20000000000000 : ℝ)^3293 := by
    have hnat : (5244742929 : ℕ)^4317*20000000000000^3293 ≤ 8582205288003^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244742929 10000000000 8582205288003 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348822043/10000000000 : ℝ), (-529098669/2500000000 : ℝ), (5244742929/10000000000 : ℝ)] ![(22015400364251/50000000000000 : ℝ), (52232691277/400000000000 : ℝ), (8582205288003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348822043/10000000000 : ℝ)|^4317 ≤ (22015400364251/50000000000000 : ℝ)^3293
        have hw : |(5348822043/10000000000 : ℝ)|=(5348822043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529098669/2500000000 : ℝ)|^4317 ≤ (52232691277/400000000000 : ℝ)^3293
        have hw : |(-529098669/2500000000 : ℝ)|=(529098669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244742929/10000000000 : ℝ)|^4317 ≤ (8582205288003/20000000000000 : ℝ)^3293
        have hw : |(5244742929/10000000000 : ℝ)|=(5244742929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s5_2 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674411029/5000000000 : ℝ)*x 0 + (655592867/1250000000 : ℝ)*x 1 + (-1058197323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674411029/5000000000 : ℝ)^4317 ≤ (44030800890377/100000000000000 : ℝ)^3293 := by
    have hnat : (2674411029 : ℕ)^4317*100000000000000^3293 ≤ 44030800890377^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674411029 5000000000 44030800890377 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655592867/1250000000 : ℝ)^4317 ≤ (42911026515097/100000000000000 : ℝ)^3293 := by
    have hnat : (655592867 : ℕ)^4317*100000000000000^3293 ≤ 42911026515097^3293*1250000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655592867 1250000000 42911026515097 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058197323/5000000000 : ℝ)^4317 ≤ (13058172576591/100000000000000 : ℝ)^3293 := by
    have hnat : (1058197323 : ℕ)^4317*100000000000000^3293 ≤ 13058172576591^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058197323 5000000000 13058172576591 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674411029/5000000000 : ℝ), (655592867/1250000000 : ℝ), (-1058197323/5000000000 : ℝ)] ![(44030800890377/100000000000000 : ℝ), (42911026515097/100000000000000 : ℝ), (13058172576591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674411029/5000000000 : ℝ)|^4317 ≤ (44030800890377/100000000000000 : ℝ)^3293
        have hw : |(2674411029/5000000000 : ℝ)|=(2674411029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655592867/1250000000 : ℝ)|^4317 ≤ (42911026515097/100000000000000 : ℝ)^3293
        have hw : |(655592867/1250000000 : ℝ)|=(655592867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1058197323/5000000000 : ℝ)|^4317 ≤ (13058172576591/100000000000000 : ℝ)^3293
        have hw : |(-1058197323/5000000000 : ℝ)|=(1058197323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s5_3 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135084023/312500000 : ℝ)*x 0 + (2074793593/5000000000 : ℝ)*x 1 + (4502476401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135084023/312500000 : ℝ)^4317 ≤ (33303283364811/100000000000000 : ℝ)^3293 := by
    have hnat : (135084023 : ℕ)^4317*100000000000000^3293 ≤ 33303283364811^3293*312500000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135084023 312500000 33303283364811 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074793593/5000000000 : ℝ)^4317 ≤ (7891484226977/25000000000000 : ℝ)^3293 := by
    have hnat : (2074793593 : ℕ)^4317*25000000000000^3293 ≤ 7891484226977^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074793593 5000000000 7891484226977 25000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502476401/10000000000 : ℝ)^4317 ≤ (17565389858857/50000000000000 : ℝ)^3293 := by
    have hnat : (4502476401 : ℕ)^4317*50000000000000^3293 ≤ 17565389858857^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502476401 10000000000 17565389858857 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135084023/312500000 : ℝ), (2074793593/5000000000 : ℝ), (4502476401/10000000000 : ℝ)] ![(33303283364811/100000000000000 : ℝ), (7891484226977/25000000000000 : ℝ), (17565389858857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135084023/312500000 : ℝ)|^4317 ≤ (33303283364811/100000000000000 : ℝ)^3293
        have hw : |(135084023/312500000 : ℝ)|=(135084023/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2074793593/5000000000 : ℝ)|^4317 ≤ (7891484226977/25000000000000 : ℝ)^3293
        have hw : |(2074793593/5000000000 : ℝ)|=(2074793593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502476401/10000000000 : ℝ)|^4317 ≤ (17565389858857/50000000000000 : ℝ)^3293
        have hw : |(4502476401/10000000000 : ℝ)|=(4502476401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s5_4 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2031053717/10000000000 : ℝ)*x 0 + (2622672883/5000000000 : ℝ)*x 1 + (5411668907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031053717/10000000000 : ℝ)^4317 ≤ (12372248264981/100000000000000 : ℝ)^3293 := by
    have hnat : (2031053717 : ℕ)^4317*100000000000000^3293 ≤ 12372248264981^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031053717 10000000000 12372248264981 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622672883/5000000000 : ℝ)^4317 ≤ (42917492543873/100000000000000 : ℝ)^3293 := by
    have hnat : (2622672883 : ℕ)^4317*100000000000000^3293 ≤ 42917492543873^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622672883 5000000000 42917492543873 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411668907/10000000000 : ℝ)^4317 ≤ (22355129590703/50000000000000 : ℝ)^3293 := by
    have hnat : (5411668907 : ℕ)^4317*50000000000000^3293 ≤ 22355129590703^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411668907 10000000000 22355129590703 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2031053717/10000000000 : ℝ), (2622672883/5000000000 : ℝ), (5411668907/10000000000 : ℝ)] ![(12372248264981/100000000000000 : ℝ), (42917492543873/100000000000000 : ℝ), (22355129590703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2031053717/10000000000 : ℝ)|^4317 ≤ (12372248264981/100000000000000 : ℝ)^3293
        have hw : |(-2031053717/10000000000 : ℝ)|=(2031053717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622672883/5000000000 : ℝ)|^4317 ≤ (42917492543873/100000000000000 : ℝ)^3293
        have hw : |(2622672883/5000000000 : ℝ)|=(2622672883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411668907/10000000000 : ℝ)|^4317 ≤ (22355129590703/50000000000000 : ℝ)^3293
        have hw : |(5411668907/10000000000 : ℝ)|=(5411668907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s5_5 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326398983/2500000000 : ℝ)*x 0 + (-974734319/5000000000 : ℝ)*x 1 + (2705834459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326398983/2500000000 : ℝ)^4317 ≤ (43564905931653/100000000000000 : ℝ)^3293 := by
    have hnat : (1326398983 : ℕ)^4317*100000000000000^3293 ≤ 43564905931653^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326398983 2500000000 43564905931653 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974734319/5000000000 : ℝ)^4317 ≤ (11724834751987/100000000000000 : ℝ)^3293 := by
    have hnat : (974734319 : ℕ)^4317*100000000000000^3293 ≤ 11724834751987^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974734319 5000000000 11724834751987 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705834459/5000000000 : ℝ)^4317 ≤ (44710259300547/100000000000000 : ℝ)^3293 := by
    have hnat : (2705834459 : ℕ)^4317*100000000000000^3293 ≤ 44710259300547^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705834459 5000000000 44710259300547 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326398983/2500000000 : ℝ), (-974734319/5000000000 : ℝ), (2705834459/5000000000 : ℝ)] ![(43564905931653/100000000000000 : ℝ), (11724834751987/100000000000000 : ℝ), (44710259300547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326398983/2500000000 : ℝ)|^4317 ≤ (43564905931653/100000000000000 : ℝ)^3293
        have hw : |(1326398983/2500000000 : ℝ)|=(1326398983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-974734319/5000000000 : ℝ)|^4317 ≤ (11724834751987/100000000000000 : ℝ)^3293
        have hw : |(-974734319/5000000000 : ℝ)|=(974734319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705834459/5000000000 : ℝ)|^4317 ≤ (44710259300547/100000000000000 : ℝ)^3293
        have hw : |(2705834459/5000000000 : ℝ)|=(2705834459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s5_6 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305595957/10000000000 : ℝ)*x 0 + (2705834441/5000000000 : ℝ)*x 1 + (-1949468653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305595957/10000000000 : ℝ)^4317 ≤ (8712981240153/20000000000000 : ℝ)^3293 := by
    have hnat : (5305595957 : ℕ)^4317*20000000000000^3293 ≤ 8712981240153^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305595957 10000000000 8712981240153 20000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705834441/5000000000 : ℝ)^4317 ≤ (44710258910633/100000000000000 : ℝ)^3293 := by
    have hnat : (2705834441 : ℕ)^4317*100000000000000^3293 ≤ 44710258910633^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705834441 5000000000 44710258910633 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949468653/10000000000 : ℝ)^4317 ≤ (11724834870257/100000000000000 : ℝ)^3293 := by
    have hnat : (1949468653 : ℕ)^4317*100000000000000^3293 ≤ 11724834870257^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949468653 10000000000 11724834870257 100000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305595957/10000000000 : ℝ), (2705834441/5000000000 : ℝ), (-1949468653/10000000000 : ℝ)] ![(8712981240153/20000000000000 : ℝ), (44710258910633/100000000000000 : ℝ), (11724834870257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305595957/10000000000 : ℝ)|^4317 ≤ (8712981240153/20000000000000 : ℝ)^3293
        have hw : |(5305595957/10000000000 : ℝ)|=(5305595957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705834441/5000000000 : ℝ)|^4317 ≤ (44710258910633/100000000000000 : ℝ)^3293
        have hw : |(2705834441/5000000000 : ℝ)|=(2705834441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1949468653/10000000000 : ℝ)|^4317 ≤ (11724834870257/100000000000000 : ℝ)^3293
        have hw : |(-1949468653/10000000000 : ℝ)|=(1949468653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1357_s5_7 (p : ℝ) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080678583/2500000000 : ℝ)*x 0 + (4501206571/10000000000 : ℝ)*x 1 + (2075431807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080678583/2500000000 : ℝ)^4317 ≤ (16651770942929/50000000000000 : ℝ)^3293 := by
    have hnat : (1080678583 : ℕ)^4317*50000000000000^3293 ≤ 16651770942929^3293*2500000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080678583 2500000000 16651770942929 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501206571/10000000000 : ℝ)^4317 ≤ (17558895695579/50000000000000 : ℝ)^3293 := by
    have hnat : (4501206571 : ℕ)^4317*50000000000000^3293 ≤ 17558895695579^3293*10000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501206571 10000000000 17558895695579 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2075431807/5000000000 : ℝ)^4317 ≤ (15789333348371/50000000000000 : ℝ)^3293 := by
    have hnat : (2075431807 : ℕ)^4317*50000000000000^3293 ≤ 15789333348371^3293*5000000000^4317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075431807 5000000000 15789333348371 50000000000000 4317 3293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4317/1024 : ℝ)) 4317 3293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080678583/2500000000 : ℝ), (4501206571/10000000000 : ℝ), (2075431807/5000000000 : ℝ)] ![(16651770942929/50000000000000 : ℝ), (17558895695579/50000000000000 : ℝ), (15789333348371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080678583/2500000000 : ℝ)|^4317 ≤ (16651770942929/50000000000000 : ℝ)^3293
        have hw : |(1080678583/2500000000 : ℝ)|=(1080678583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501206571/10000000000 : ℝ)|^4317 ≤ (17558895695579/50000000000000 : ℝ)^3293
        have hw : |(4501206571/10000000000 : ℝ)|=(4501206571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2075431807/5000000000 : ℝ)|^4317 ≤ (15789333348371/50000000000000 : ℝ)^3293
        have hw : |(2075431807/5000000000 : ℝ)|=(2075431807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1357_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11177/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3681/25000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5569/50000 : ℝ) ^ (1079/256 : ℝ) ≤ (1920752190585189/20000000000000000000 : ℝ) := by
    have hpowers : (5569/50000 : ℝ)^1079 ≤ (1920752190585189/20000000000000000000 : ℝ)^256 := by
      have hnat : (5569 : ℕ)^1079*20000000000000000000^256 ≤ 1920752190585189^256*50000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5569 50000 1920752190585189 20000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5569/50000 : ℝ)) (X := (1920752190585189/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2953/20000 : ℝ) ^ (1079/256 : ℝ) ≤ (31510029118537137/100000000000000000000 : ℝ) := by
    have hpowers : (2953/20000 : ℝ)^1079 ≤ (31510029118537137/100000000000000000000 : ℝ)^256 := by
      have hnat : (2953 : ℕ)^1079*100000000000000000000^256 ≤ 31510029118537137^256*20000^1079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2953 20000 31510029118537137 100000000000000000000 1079 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2953/20000 : ℝ)) (X := (31510029118537137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001920752190585189/10000000000000000000 : ℝ) ≤ (2500113919496271/2500000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (10001920752190585189/10000000000000000000 : ℝ)^256 ≤ (2500113919496271/2500000000000000 : ℝ)^1079 := by
      have hnat : (10001920752190585189 : ℕ)^256*2500000000000000^1079 ≤ 2500113919496271^1079*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001920752190585189 10000000000000000000 2500113919496271 2500000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500113919496271/2500000000000000 : ℝ)) (X := (10001920752190585189/10000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020556895035731541/50000000000000000000 : ℝ) ≤ (1250121912423019/1250000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50020556895035731541/50000000000000000000 : ℝ)^256 ≤ (1250121912423019/1250000000000000 : ℝ)^1079 := by
      have hnat : (50020556895035731541 : ℕ)^256*1250000000000000^1079 ≤ 1250121912423019^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020556895035731541 50000000000000000000 1250121912423019 1250000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250121912423019/1250000000000000 : ℝ)) (X := (50020556895035731541/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031510029118537137/50000000000000000000 : ℝ) ≤ (500074746039161/500000000000000 : ℝ) ^ (1079/256 : ℝ) := by
    have hpowers : (50031510029118537137/50000000000000000000 : ℝ)^256 ≤ (500074746039161/500000000000000 : ℝ)^1079 := by
      have hnat : (50031510029118537137 : ℕ)^256*500000000000000^1079 ≤ 500074746039161^1079*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031510029118537137 50000000000000000000 500074746039161 500000000000000 256 1079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500074746039161/500000000000000 : ℝ)) (X := (50031510029118537137/50000000000000000000 : ℝ)) (by norm_num) 1079 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1920752190585189/20000000000000000000 : ℝ) ≤ ((362600776577662609/362700000000000000 : ℝ)+2*(129905349767/90675000000000 : ℝ)*(5569/50000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (362600776577662609/362700000000000000 : ℝ)+2*(129905349767/90675000000000 : ℝ)*(5569/50000 : ℝ)=(2500113919496271/2500000000000000 : ℝ) by norm_num, show 1+2*(1920752190585189/20000000000000000000 : ℝ)=(10001920752190585189/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31510029118537137/100000000000000000000 : ℝ)+(1920752190585189/20000000000000000000 : ℝ) ≤ ((362600776577662609/362700000000000000 : ℝ)+(129905349767/90675000000000 : ℝ)*((2953/20000 : ℝ)+(5569/50000 : ℝ)))^(1079/256 : ℝ) := by
    rw [show (362600776577662609/362700000000000000 : ℝ)+(129905349767/90675000000000 : ℝ)*((2953/20000 : ℝ)+(5569/50000 : ℝ))=(1250121912423019/1250000000000000 : ℝ) by norm_num, show 1+(31510029118537137/100000000000000000000 : ℝ)+(1920752190585189/20000000000000000000 : ℝ)=(50020556895035731541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31510029118537137/100000000000000000000 : ℝ) ≤ ((362600776577662609/362700000000000000 : ℝ)+2*(129905349767/90675000000000 : ℝ)*(2953/20000 : ℝ))^(1079/256 : ℝ) := by
    rw [show (362600776577662609/362700000000000000 : ℝ)+2*(129905349767/90675000000000 : ℝ)*(2953/20000 : ℝ)=(500074746039161/500000000000000 : ℝ) by norm_num, show 1+2*(31510029118537137/100000000000000000000 : ℝ)=(50031510029118537137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (362600776577662609/362700000000000000 : ℝ)*(X 1 0+X 2 0)+(129905349767/90675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (362600776577662609/362700000000000000 : ℝ)) (alpha := (129905349767/90675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (362600776577662609/362700000000000000 : ℝ)*(X 0 1+X 2 1)+(129905349767/90675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (362600776577662609/362700000000000000 : ℝ)) (alpha := (129905349767/90675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (362600776577662609/362700000000000000 : ℝ)*(X 0 2+X 1 2)+(129905349767/90675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1079/256 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (362600776577662609/362700000000000000 : ℝ)) (alpha := (129905349767/90675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-406208323/2000000000 : ℝ)*X 0 0+(5412274857/10000000000 : ℝ)*X 0 1+(2622371447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348822043/10000000000 : ℝ)*X 1 0+(-529098669/2500000000 : ℝ)*X 1 1+(5244742929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674411029/5000000000 : ℝ)*X 2 0+(655592867/1250000000 : ℝ)*X 2 1+(-1058197323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135084023/312500000 : ℝ)*X 0 0+(2074793593/5000000000 : ℝ)*X 0 1+(4502476401/10000000000 : ℝ)*X 0 2+(135084023/312500000 : ℝ)*X 1 0+(2074793593/5000000000 : ℝ)*X 1 1+(4502476401/10000000000 : ℝ)*X 1 2+(135084023/312500000 : ℝ)*X 2 0+(2074793593/5000000000 : ℝ)*X 2 1+(4502476401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2031053717/10000000000 : ℝ)*X 0 0+(2622672883/5000000000 : ℝ)*X 0 1+(5411668907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326398983/2500000000 : ℝ)*X 1 0+(-974734319/5000000000 : ℝ)*X 1 1+(2705834459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305595957/10000000000 : ℝ)*X 2 0+(2705834441/5000000000 : ℝ)*X 2 1+(-1949468653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080678583/2500000000 : ℝ)*X 0 0+(4501206571/10000000000 : ℝ)*X 0 1+(2075431807/5000000000 : ℝ)*X 0 2+(1080678583/2500000000 : ℝ)*X 1 0+(4501206571/10000000000 : ℝ)*X 1 1+(2075431807/5000000000 : ℝ)*X 1 2+(1080678583/2500000000 : ℝ)*X 2 0+(4501206571/10000000000 : ℝ)*X 2 1+(2075431807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1357_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2359917705366764093413/403000000000000000000000000 : ℝ) := by norm_num
    linear_combination (540283941/50000000000000 : ℝ)*(base19) + (217773843/20000000000000 : ℝ)*(base23) + (130869097/100000000000000 : ℝ)*(upper3) + (4513347/100000000000000 : ℝ)*(upper4) + (82127391/50000000000000 : ℝ)*(upper5) + (880282964117803/20000000000000 : ℝ)*(major0) + (880282964117803/20000000000000 : ℝ)*(major1) + (880282964117803/20000000000000 : ℝ)*(major2) + (5969032735679937/100000000000000 : ℝ)*(sp0) + (5969055849088851/100000000000000 : ℝ)*(sp1) + (2984527920393759/50000000000000 : ℝ)*(sp2) + (354220209803461/12500000000000 : ℝ)*(sp3) + (6048494199/25000000000000 : ℝ)*(sp4) + (2167579553/20000000000000 : ℝ)*(sp7) + (2833772516325453/100000000000000 : ℝ)*(f.failure) + (5969056929656733/100000000000000 : ℝ)*(f.sum) + (8612195451257/3627000000000000000000000000 : ℝ)*base65 + (1416363683980003/806000000000000000000000000000 : ℝ)*base67 + (80623114339997/806000000000000000000000000000 : ℝ)*base70 + (4465201013102003/806000000000000000000000000000 : ℝ)*base71 + (3202254258943/725400000000000000000000000 : ℝ)*base73 + (771169832886003/806000000000000000000000000000 : ℝ)*base75 + (7362953324403997/806000000000000000000000000000 : ℝ)*base78 + (3647075897037997/806000000000000000000000000000 : ℝ)*base80 + (6577826360707/1813500000000000000000000000 : ℝ)*base81 + (15525419/10000000000000000000000 : ℝ)*base90 + (15525419/10000000000000000000000 : ℝ)*base92 + (15525419/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1119805979153992249968253/125937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (197617169/12500000000000 : ℝ)*(base19) + (1704405989/100000000000000 : ℝ)*(base23) + (92296809/50000000000000 : ℝ)*(upper3) + (2275361/5000000000000 : ℝ)*(lower4) + (96174283/50000000000000 : ℝ)*(upper5) + (554171117984673/12500000000000 : ℝ)*(major0) + (554171117984673/12500000000000 : ℝ)*(major1) + (554171117984673/12500000000000 : ℝ)*(major2) + (32793360429/100000000000000 : ℝ)*(sp1) + (4242871099/12500000000000 : ℝ)*(sp2) + (6012391982054967/100000000000000 : ℝ)*(sp4) + (6012357607757187/100000000000000 : ℝ)*(sp5) + (1202471266936037/20000000000000 : ℝ)*(sp6) + (2854345609307799/100000000000000 : ℝ)*(sp7) + (2854345609307799/100000000000000 : ℝ)*(f.failure) + (6012391982054967/100000000000000 : ℝ)*(f.sum) + (28325078136899/6045000000000000000000000000 : ℝ)*base65 + (4134424219206623/503750000000000000000000000000 : ℝ)*base67 + (4749342894183377/503750000000000000000000000000 : ℝ)*base70 + (9559455040026623/503750000000000000000000000000 : ℝ)*base71 + (233618632349/6045000000000000000000000000 : ℝ)*base73 + (7694446309950877/503750000000000000000000000000 : ℝ)*base76 + (5827107691589123/503750000000000000000000000000 : ℝ)*base77 + (7074189951356623/503750000000000000000000000000 : ℝ)*base79 + (14660216973001/6045000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (73399377/10000000000000000000000 : ℝ)*base90 + (73399377/10000000000000000000000 : ℝ)*base92 + (73399377/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1357_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1357_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1357_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2487/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1357_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1357_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1357_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1079/256 : ℝ) ≤ p) (hpb : p ≤ (4317/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155319977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2487/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1357_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

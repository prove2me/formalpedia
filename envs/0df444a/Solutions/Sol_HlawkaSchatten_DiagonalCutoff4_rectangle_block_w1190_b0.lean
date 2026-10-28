-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1190_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:53:06.510432+00:00
-- url     : https://prove2.me/submissions/5dd81822-9566-472c-aad4-7007462b8b2f

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
theorem support_rectangle_w1190_s0_0 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-938355719/5000000000 : ℝ)*x 0 + (3021651159/5000000000 : ℝ)*x 1 + (2393256477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (938355719/5000000000 : ℝ)^8383 ≤ (10926951449437/100000000000000 : ℝ)^6335 := by
    have hnat : (938355719 : ℕ)^8383*100000000000000^6335 ≤ 10926951449437^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938355719 5000000000 10926951449437 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3021651159/5000000000 : ℝ)^8383 ≤ (51352779009677/100000000000000 : ℝ)^6335 := by
    have hnat : (3021651159 : ℕ)^8383*100000000000000^6335 ≤ 51352779009677^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021651159 5000000000 51352779009677 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2393256477/5000000000 : ℝ)^8383 ≤ (18860134761733/50000000000000 : ℝ)^6335 := by
    have hnat : (2393256477 : ℕ)^8383*50000000000000^6335 ≤ 18860134761733^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393256477 5000000000 18860134761733 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-938355719/5000000000 : ℝ), (3021651159/5000000000 : ℝ), (2393256477/5000000000 : ℝ)] ![(10926951449437/100000000000000 : ℝ), (51352779009677/100000000000000 : ℝ), (18860134761733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-938355719/5000000000 : ℝ)|^8383 ≤ (10926951449437/100000000000000 : ℝ)^6335
        have hw : |(-938355719/5000000000 : ℝ)|=(938355719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3021651159/5000000000 : ℝ)|^8383 ≤ (51352779009677/100000000000000 : ℝ)^6335
        have hw : |(3021651159/5000000000 : ℝ)|=(3021651159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2393256477/5000000000 : ℝ)|^8383 ≤ (18860134761733/50000000000000 : ℝ)^6335
        have hw : |(2393256477/5000000000 : ℝ)|=(2393256477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s0_1 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757044523/5000000000 : ℝ)*x 0 + (-649154839/2500000000 : ℝ)*x 1 + (1196628237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757044523/5000000000 : ℝ)^8383 ≤ (45487969594221/100000000000000 : ℝ)^6335 := by
    have hnat : (2757044523 : ℕ)^8383*100000000000000^6335 ≤ 45487969594221^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757044523 5000000000 45487969594221 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649154839/2500000000 : ℝ)^8383 ≤ (524742529153/3125000000000 : ℝ)^6335 := by
    have hnat : (649154839 : ℕ)^8383*3125000000000^6335 ≤ 524742529153^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649154839 2500000000 524742529153 3125000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196628237/2500000000 : ℝ)^8383 ≤ (37720269460897/100000000000000 : ℝ)^6335 := by
    have hnat : (1196628237 : ℕ)^8383*100000000000000^6335 ≤ 37720269460897^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196628237 2500000000 37720269460897 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757044523/5000000000 : ℝ), (-649154839/2500000000 : ℝ), (1196628237/2500000000 : ℝ)] ![(45487969594221/100000000000000 : ℝ), (524742529153/3125000000000 : ℝ), (37720269460897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757044523/5000000000 : ℝ)|^8383 ≤ (45487969594221/100000000000000 : ℝ)^6335
        have hw : |(2757044523/5000000000 : ℝ)|=(2757044523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-649154839/2500000000 : ℝ)|^8383 ≤ (524742529153/3125000000000 : ℝ)^6335
        have hw : |(-649154839/2500000000 : ℝ)|=(649154839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196628237/2500000000 : ℝ)|^8383 ≤ (37720269460897/100000000000000 : ℝ)^6335
        have hw : |(1196628237/2500000000 : ℝ)|=(1196628237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s0_2 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (275704471/500000000 : ℝ)*x 0 + (95730251/200000000 : ℝ)*x 1 + (-2596619363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275704471/500000000 : ℝ)^8383 ≤ (45487973676919/100000000000000 : ℝ)^6335 := by
    have hnat : (275704471 : ℕ)^8383*100000000000000^6335 ≤ 45487973676919^6335*500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275704471 500000000 45487973676919 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95730251/200000000 : ℝ)^8383 ≤ (18860132655241/50000000000000 : ℝ)^6335 := by
    have hnat : (95730251 : ℕ)^8383*50000000000000^6335 ≤ 18860132655241^6335*200000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95730251 200000000 18860132655241 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2596619363/10000000000 : ℝ)^8383 ≤ (16791760992797/100000000000000 : ℝ)^6335 := by
    have hnat : (2596619363 : ℕ)^8383*100000000000000^6335 ≤ 16791760992797^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596619363 10000000000 16791760992797 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275704471/500000000 : ℝ), (95730251/200000000 : ℝ), (-2596619363/10000000000 : ℝ)] ![(45487973676919/100000000000000 : ℝ), (18860132655241/50000000000000 : ℝ), (16791760992797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275704471/500000000 : ℝ)|^8383 ≤ (45487973676919/100000000000000 : ℝ)^6335
        have hw : |(275704471/500000000 : ℝ)|=(275704471/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(95730251/200000000 : ℝ)|^8383 ≤ (18860132655241/50000000000000 : ℝ)^6335
        have hw : |(95730251/200000000 : ℝ)|=(95730251/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2596619363/10000000000 : ℝ)|^8383 ≤ (16791760992797/100000000000000 : ℝ)^6335
        have hw : |(-2596619363/10000000000 : ℝ)|=(2596619363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s0_3 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4197136417/10000000000 : ℝ)*x 0 + (3118958743/10000000000 : ℝ)*x 1 + (352679437/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197136417/10000000000 : ℝ)^8383 ≤ (15850030451851/50000000000000 : ℝ)^6335 := by
    have hnat : (4197136417 : ℕ)^8383*50000000000000^6335 ≤ 15850030451851^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197136417 10000000000 15850030451851 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118958743/10000000000 : ℝ)^8383 ≤ (4280173418993/20000000000000 : ℝ)^6335 := by
    have hnat : (3118958743 : ℕ)^8383*20000000000000^6335 ≤ 4280173418993^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118958743 10000000000 4280173418993 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352679437/625000000 : ℝ)^8383 ≤ (5862383997619/12500000000000 : ℝ)^6335 := by
    have hnat : (352679437 : ℕ)^8383*12500000000000^6335 ≤ 5862383997619^6335*625000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352679437 625000000 5862383997619 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197136417/10000000000 : ℝ), (3118958743/10000000000 : ℝ), (352679437/625000000 : ℝ)] ![(15850030451851/50000000000000 : ℝ), (4280173418993/20000000000000 : ℝ), (5862383997619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197136417/10000000000 : ℝ)|^8383 ≤ (15850030451851/50000000000000 : ℝ)^6335
        have hw : |(4197136417/10000000000 : ℝ)|=(4197136417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118958743/10000000000 : ℝ)|^8383 ≤ (4280173418993/20000000000000 : ℝ)^6335
        have hw : |(3118958743/10000000000 : ℝ)|=(3118958743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(352679437/625000000 : ℝ)|^8383 ≤ (5862383997619/12500000000000 : ℝ)^6335
        have hw : |(352679437/625000000 : ℝ)|=(352679437/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s0_4 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-940858621/5000000000 : ℝ)*x 0 + (602363583/1250000000 : ℝ)*x 1 + (3004882133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940858621/5000000000 : ℝ)^8383 ≤ (5482768082107/50000000000000 : ℝ)^6335 := by
    have hnat : (940858621 : ℕ)^8383*50000000000000^6335 ≤ 5482768082107^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940858621 5000000000 5482768082107 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (602363583/1250000000 : ℝ)^8383 ≤ (19029233373849/50000000000000 : ℝ)^6335 := by
    have hnat : (602363583 : ℕ)^8383*50000000000000^6335 ≤ 19029233373849^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602363583 1250000000 19029233373849 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3004882133/5000000000 : ℝ)^8383 ≤ (50975997082701/100000000000000 : ℝ)^6335 := by
    have hnat : (3004882133 : ℕ)^8383*100000000000000^6335 ≤ 50975997082701^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3004882133 5000000000 50975997082701 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-940858621/5000000000 : ℝ), (602363583/1250000000 : ℝ), (3004882133/5000000000 : ℝ)] ![(5482768082107/50000000000000 : ℝ), (19029233373849/50000000000000 : ℝ), (50975997082701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-940858621/5000000000 : ℝ)|^8383 ≤ (5482768082107/50000000000000 : ℝ)^6335
        have hw : |(-940858621/5000000000 : ℝ)|=(940858621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(602363583/1250000000 : ℝ)|^8383 ≤ (19029233373849/50000000000000 : ℝ)^6335
        have hw : |(602363583/1250000000 : ℝ)|=(602363583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3004882133/5000000000 : ℝ)|^8383 ≤ (50975997082701/100000000000000 : ℝ)^6335
        have hw : |(3004882133/5000000000 : ℝ)|=(3004882133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s0_5 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5172365217/10000000000 : ℝ)*x 0 + (-1373368037/10000000000 : ℝ)*x 1 + (1201952779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172365217/10000000000 : ℝ)^8383 ≤ (20897756651599/50000000000000 : ℝ)^6335 := by
    have hnat : (5172365217 : ℕ)^8383*50000000000000^6335 ≤ 20897756651599^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172365217 10000000000 20897756651599 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373368037/10000000000 : ℝ)^8383 ≤ (180712344153/2500000000000 : ℝ)^6335 := by
    have hnat : (1373368037 : ℕ)^8383*2500000000000^6335 ≤ 180712344153^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373368037 10000000000 180712344153 2500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1201952779/2000000000 : ℝ)^8383 ≤ (12743998229617/25000000000000 : ℝ)^6335 := by
    have hnat : (1201952779 : ℕ)^8383*25000000000000^6335 ≤ 12743998229617^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201952779 2000000000 12743998229617 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172365217/10000000000 : ℝ), (-1373368037/10000000000 : ℝ), (1201952779/2000000000 : ℝ)] ![(20897756651599/50000000000000 : ℝ), (180712344153/2500000000000 : ℝ), (12743998229617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172365217/10000000000 : ℝ)|^8383 ≤ (20897756651599/50000000000000 : ℝ)^6335
        have hw : |(5172365217/10000000000 : ℝ)|=(5172365217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1373368037/10000000000 : ℝ)|^8383 ≤ (180712344153/2500000000000 : ℝ)^6335
        have hw : |(-1373368037/10000000000 : ℝ)|=(1373368037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1201952779/2000000000 : ℝ)|^8383 ≤ (12743998229617/25000000000000 : ℝ)^6335
        have hw : |(1201952779/2000000000 : ℝ)|=(1201952779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s0_6 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5172365141/10000000000 : ℝ)*x 0 + (600976411/1000000000 : ℝ)*x 1 + (-1373367807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172365141/10000000000 : ℝ)^8383 ≤ (20897756245271/50000000000000 : ℝ)^6335 := by
    have hnat : (5172365141 : ℕ)^8383*50000000000000^6335 ≤ 20897756245271^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172365141 10000000000 20897756245271 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600976411/1000000000 : ℝ)^8383 ≤ (50975995331703/100000000000000 : ℝ)^6335 := by
    have hnat : (600976411 : ℕ)^8383*100000000000000^6335 ≤ 50975995331703^6335*1000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600976411 1000000000 50975995331703 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1373367807/10000000000 : ℝ)^8383 ≤ (3614246082099/50000000000000 : ℝ)^6335 := by
    have hnat : (1373367807 : ℕ)^8383*50000000000000^6335 ≤ 3614246082099^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373367807 10000000000 3614246082099 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172365141/10000000000 : ℝ), (600976411/1000000000 : ℝ), (-1373367807/10000000000 : ℝ)] ![(20897756245271/50000000000000 : ℝ), (50975995331703/100000000000000 : ℝ), (3614246082099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172365141/10000000000 : ℝ)|^8383 ≤ (20897756245271/50000000000000 : ℝ)^6335
        have hw : |(5172365141/10000000000 : ℝ)|=(5172365141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600976411/1000000000 : ℝ)|^8383 ≤ (50975995331703/100000000000000 : ℝ)^6335
        have hw : |(600976411/1000000000 : ℝ)|=(600976411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1373367807/10000000000 : ℝ)|^8383 ≤ (3614246082099/50000000000000 : ℝ)^6335
        have hw : |(-1373367807/10000000000 : ℝ)|=(1373367807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s0_7 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2103594647/5000000000 : ℝ)*x 0 + (2788906349/5000000000 : ℝ)*x 1 + (1593155529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103594647/5000000000 : ℝ)^8383 ≤ (31800572980281/100000000000000 : ℝ)^6335 := by
    have hnat : (2103594647 : ℕ)^8383*100000000000000^6335 ≤ 31800572980281^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103594647 5000000000 31800572980281 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2788906349/5000000000 : ℝ)^8383 ≤ (46184892424841/100000000000000 : ℝ)^6335 := by
    have hnat : (2788906349 : ℕ)^8383*100000000000000^6335 ≤ 46184892424841^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788906349 5000000000 46184892424841 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1593155529/5000000000 : ℝ)^8383 ≤ (11007267292847/50000000000000 : ℝ)^6335 := by
    have hnat : (1593155529 : ℕ)^8383*50000000000000^6335 ≤ 11007267292847^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593155529 5000000000 11007267292847 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103594647/5000000000 : ℝ), (2788906349/5000000000 : ℝ), (1593155529/5000000000 : ℝ)] ![(31800572980281/100000000000000 : ℝ), (46184892424841/100000000000000 : ℝ), (11007267292847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103594647/5000000000 : ℝ)|^8383 ≤ (31800572980281/100000000000000 : ℝ)^6335
        have hw : |(2103594647/5000000000 : ℝ)|=(2103594647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2788906349/5000000000 : ℝ)|^8383 ≤ (46184892424841/100000000000000 : ℝ)^6335
        have hw : |(2788906349/5000000000 : ℝ)|=(2788906349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1593155529/5000000000 : ℝ)|^8383 ≤ (11007267292847/50000000000000 : ℝ)^6335
        have hw : |(1593155529/5000000000 : ℝ)|=(1593155529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1190_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (609/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1727/6250 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4191/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4191 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4191*1^1024 ≤ 0^1024*1^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4191/1024 : ℝ) ≤ (2351373951557550133/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4191 ≤ (2351373951557550133/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4191*100000000000000000000^1024 ≤ 2351373951557550133^1024*5^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2351373951557550133 100000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2351373951557550133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4191 := by
      have hnat : (1 : ℕ)^1024*1^4191 ≤ 1^4191*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102351373951557550133/100000000000000000000 : ℝ) ≤ (5028474170617289/5000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (102351373951557550133/100000000000000000000 : ℝ)^1024 ≤ (5028474170617289/5000000000000000 : ℝ)^4191 := by
      have hnat : (102351373951557550133 : ℕ)^1024*5000000000000000^4191 ≤ 5028474170617289^4191*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102351373951557550133 100000000000000000000 5028474170617289 5000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028474170617289/5000000000000000 : ℝ)) (X := (102351373951557550133/100000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52351373951557550133/50000000000000000000 : ℝ) ≤ (2528474170617289/2500000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (52351373951557550133/50000000000000000000 : ℝ)^1024 ≤ (2528474170617289/2500000000000000 : ℝ)^4191 := by
      have hnat : (52351373951557550133 : ℕ)^1024*2500000000000000^4191 ≤ 2528474170617289^4191*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52351373951557550133 50000000000000000000 2528474170617289 2500000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528474170617289/2500000000000000 : ℝ)) (X := (52351373951557550133/50000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28474170617289/2000000000000000 : ℝ)*(0 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28474170617289/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2351373951557550133/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28474170617289/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4191/1024 : ℝ) := by
    rw [show (1 : ℝ)+(28474170617289/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028474170617289/5000000000000000 : ℝ) by norm_num, show 1+(2351373951557550133/100000000000000000000 : ℝ)+(0 : ℝ)=(102351373951557550133/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2351373951557550133/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28474170617289/2000000000000000 : ℝ)*(2/5 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(28474170617289/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528474170617289/2500000000000000 : ℝ) by norm_num, show 1+2*(2351373951557550133/100000000000000000000 : ℝ)=(52351373951557550133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28474170617289/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28474170617289/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28474170617289/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28474170617289/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28474170617289/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28474170617289/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-938355719/5000000000 : ℝ)*X 0 0+(3021651159/5000000000 : ℝ)*X 0 1+(2393256477/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757044523/5000000000 : ℝ)*X 1 0+(-649154839/2500000000 : ℝ)*X 1 1+(1196628237/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((275704471/500000000 : ℝ)*X 2 0+(95730251/200000000 : ℝ)*X 2 1+(-2596619363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4197136417/10000000000 : ℝ)*X 0 0+(3118958743/10000000000 : ℝ)*X 0 1+(352679437/625000000 : ℝ)*X 0 2+(4197136417/10000000000 : ℝ)*X 1 0+(3118958743/10000000000 : ℝ)*X 1 1+(352679437/625000000 : ℝ)*X 1 2+(4197136417/10000000000 : ℝ)*X 2 0+(3118958743/10000000000 : ℝ)*X 2 1+(352679437/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-940858621/5000000000 : ℝ)*X 0 0+(602363583/1250000000 : ℝ)*X 0 1+(3004882133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5172365217/10000000000 : ℝ)*X 1 0+(-1373368037/10000000000 : ℝ)*X 1 1+(1201952779/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5172365141/10000000000 : ℝ)*X 2 0+(600976411/1000000000 : ℝ)*X 2 1+(-1373367807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2103594647/5000000000 : ℝ)*X 0 0+(2788906349/5000000000 : ℝ)*X 0 1+(1593155529/5000000000 : ℝ)*X 0 2+(2103594647/5000000000 : ℝ)*X 1 0+(2788906349/5000000000 : ℝ)*X 1 1+(1593155529/5000000000 : ℝ)*X 1 2+(2103594647/5000000000 : ℝ)*X 2 0+(2788906349/5000000000 : ℝ)*X 2 1+(1593155529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23538387458246081660511/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9018281/12500000000000 : ℝ)*(base1) + (453053969/25000000000000 : ℝ)*(base19) + (173200701/10000000000000 : ℝ)*(base23) + (134177287/100000000000000 : ℝ)*(base24) + (107679149/25000000000000 : ℝ)*(upper3) + (9311748171179/1562500000000 : ℝ)*(major0) + (9311748171179/1562500000000 : ℝ)*(major1) + (9311748171179/1562500000000 : ℝ)*(major2) + (99460540339921/12500000000000 : ℝ)*(sp0) + (795686354719249/100000000000000 : ℝ)*(sp1) + (795686300750829/100000000000000 : ℝ)*(sp2) + (198106042113453/50000000000000 : ℝ)*(sp3) + (1958181003/50000000000000 : ℝ)*(sp4) + (638305299/20000000000000 : ℝ)*(sp7) + (396215347899649/100000000000000 : ℝ)*(f.failure) + (397844083467563/50000000000000 : ℝ)*(f.sum) + (4636014986269/1562500000000000000000000000 : ℝ)*base66 + (12370130073769/3125000000000000000000000000 : ℝ)*base68 + (6696509132481/3125000000000000000000000000 : ℝ)*base69 + (1346310207481/3125000000000000000000000000 : ℝ)*base71 + (5930151436269/1562500000000000000000000000 : ℝ)*base74 + (11615992307481/3125000000000000000000000000 : ℝ)*base75 + (7806448311269/3125000000000000000000000000 : ℝ)*base78 + (8181658017519/3125000000000000000000000000 : ℝ)*base80 + (17101254905587/3125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7040429/2000000000000000000000 : ℝ)*base89 + (7040429/2000000000000000000000 : ℝ)*base91 + (7040429/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (115164147360638682841713/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23590041/50000000000000 : ℝ)*(base1) + (1189852013/100000000000000 : ℝ)*(base19) + (1182330477/100000000000000 : ℝ)*(base23) + (60490461/50000000000000 : ℝ)*(upper3) + (29361741/20000000000000 : ℝ)*(upper5) + (314469985488261/50000000000000 : ℝ)*(major0) + (314469985488261/50000000000000 : ℝ)*(major1) + (314469985488261/50000000000000 : ℝ)*(major2) + (2405801787/100000000000000 : ℝ)*(sp1) + (2478709583/100000000000000 : ℝ)*(sp2) + (419866268947673/50000000000000 : ℝ)*(sp4) + (104966111882683/12500000000000 : ℝ)*(sp5) + (209932207418801/25000000000000 : ℝ)*(sp6) + (418147250505499/100000000000000 : ℝ)*(sp7) + (418147297685581/100000000000000 : ℝ)*(f.failure) + (6560410083713/781250000000 : ℝ)*(f.sum) + (113531834444429/50000000000000000000000000000 : ℝ)*base65 + (100979971455571/100000000000000000000000000000 : ℝ)*base68 + (260389035344429/100000000000000000000000000000 : ℝ)*base69 + (9964626455571/100000000000000000000000000000 : ℝ)*base72 + (109119885044429/50000000000000000000000000000 : ℝ)*base73 + (10768396655571/100000000000000000000000000000 : ℝ)*base76 + (152040100144429/100000000000000000000000000000 : ℝ)*base77 + (63601706055571/100000000000000000000000000000 : ℝ)*base80 + (257475698894429/50000000000000000000000000000 : ℝ)*base81 + (3844599/2000000000000000000000 : ℝ)*base90 + (3844599/2000000000000000000000 : ℝ)*base92 + (3844599/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1190_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (609/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1727/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1190_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1190_s1_0 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077902333/10000000000 : ℝ)*x 0 + (5688870823/10000000000 : ℝ)*x 1 + (2506077663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077902333/10000000000 : ℝ)^8383 ≤ (2500660275019/20000000000000 : ℝ)^6335 := by
    have hnat : (2077902333 : ℕ)^8383*20000000000000^6335 ≤ 2500660275019^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077902333 10000000000 2500660275019 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5688870823/10000000000 : ℝ)^8383 ≤ (5925705915499/12500000000000 : ℝ)^6335 := by
    have hnat : (5688870823 : ℕ)^8383*12500000000000^6335 ≤ 5925705915499^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688870823 10000000000 5925705915499 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2506077663/5000000000 : ℝ)^8383 ≤ (40091051281797/100000000000000 : ℝ)^6335 := by
    have hnat : (2506077663 : ℕ)^8383*100000000000000^6335 ≤ 40091051281797^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506077663 5000000000 40091051281797 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077902333/10000000000 : ℝ), (5688870823/10000000000 : ℝ), (2506077663/5000000000 : ℝ)] ![(2500660275019/20000000000000 : ℝ), (5925705915499/12500000000000 : ℝ), (40091051281797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077902333/10000000000 : ℝ)|^8383 ≤ (2500660275019/20000000000000 : ℝ)^6335
        have hw : |(-2077902333/10000000000 : ℝ)|=(2077902333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5688870823/10000000000 : ℝ)|^8383 ≤ (5925705915499/12500000000000 : ℝ)^6335
        have hw : |(5688870823/10000000000 : ℝ)|=(5688870823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2506077663/5000000000 : ℝ)|^8383 ≤ (40091051281797/100000000000000 : ℝ)^6335
        have hw : |(2506077663/5000000000 : ℝ)|=(2506077663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s1_1 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5416491791/10000000000 : ℝ)*x 0 + (-305276547/1250000000 : ℝ)*x 1 + (1002431123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416491791/10000000000 : ℝ)^8383 ≤ (44425628652549/100000000000000 : ℝ)^6335 := by
    have hnat : (5416491791 : ℕ)^8383*100000000000000^6335 ≤ 44425628652549^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416491791 10000000000 44425628652549 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (305276547/1250000000 : ℝ)^8383 ≤ (19354146249/125000000000 : ℝ)^6335 := by
    have hnat : (305276547 : ℕ)^8383*125000000000^6335 ≤ 19354146249^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305276547 1250000000 19354146249 125000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002431123/2000000000 : ℝ)^8383 ≤ (10022763585189/25000000000000 : ℝ)^6335 := by
    have hnat : (1002431123 : ℕ)^8383*25000000000000^6335 ≤ 10022763585189^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002431123 2000000000 10022763585189 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416491791/10000000000 : ℝ), (-305276547/1250000000 : ℝ), (1002431123/2000000000 : ℝ)] ![(44425628652549/100000000000000 : ℝ), (19354146249/125000000000 : ℝ), (10022763585189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416491791/10000000000 : ℝ)|^8383 ≤ (44425628652549/100000000000000 : ℝ)^6335
        have hw : |(5416491791/10000000000 : ℝ)|=(5416491791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-305276547/1250000000 : ℝ)|^8383 ≤ (19354146249/125000000000 : ℝ)^6335
        have hw : |(-305276547/1250000000 : ℝ)|=(305276547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002431123/2000000000 : ℝ)|^8383 ≤ (10022763585189/25000000000000 : ℝ)^6335
        have hw : |(1002431123/2000000000 : ℝ)|=(1002431123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s1_2 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2708245433/5000000000 : ℝ)*x 0 + (78314941/156250000 : ℝ)*x 1 + (-488442561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708245433/5000000000 : ℝ)^8383 ≤ (5553202326637/12500000000000 : ℝ)^6335 := by
    have hnat : (2708245433 : ℕ)^8383*12500000000000^6335 ≤ 5553202326637^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708245433 5000000000 5553202326637 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78314941/156250000 : ℝ)^8383 ≤ (40091060786797/100000000000000 : ℝ)^6335 := by
    have hnat : (78314941 : ℕ)^8383*100000000000000^6335 ≤ 40091060786797^6335*156250000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78314941 156250000 40091060786797 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488442561/2000000000 : ℝ)^8383 ≤ (15483320598273/100000000000000 : ℝ)^6335 := by
    have hnat : (488442561 : ℕ)^8383*100000000000000^6335 ≤ 15483320598273^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488442561 2000000000 15483320598273 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708245433/5000000000 : ℝ), (78314941/156250000 : ℝ), (-488442561/2000000000 : ℝ)] ![(5553202326637/12500000000000 : ℝ), (40091060786797/100000000000000 : ℝ), (15483320598273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708245433/5000000000 : ℝ)|^8383 ≤ (5553202326637/12500000000000 : ℝ)^6335
        have hw : |(2708245433/5000000000 : ℝ)|=(2708245433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78314941/156250000 : ℝ)|^8383 ≤ (40091060786797/100000000000000 : ℝ)^6335
        have hw : |(78314941/156250000 : ℝ)|=(78314941/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-488442561/2000000000 : ℝ)|^8383 ≤ (15483320598273/100000000000000 : ℝ)^6335
        have hw : |(-488442561/2000000000 : ℝ)|=(488442561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s1_3 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (172533769/400000000 : ℝ)*x 0 + (1842983227/5000000000 : ℝ)*x 1 + (5044961683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172533769/400000000 : ℝ)^8383 ≤ (32866662435763/100000000000000 : ℝ)^6335 := by
    have hnat : (172533769 : ℕ)^8383*100000000000000^6335 ≤ 32866662435763^6335*400000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172533769 400000000 32866662435763 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842983227/5000000000 : ℝ)^8383 ≤ (13347338103691/50000000000000 : ℝ)^6335 := by
    have hnat : (1842983227 : ℕ)^8383*50000000000000^6335 ≤ 13347338103691^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842983227 5000000000 13347338103691 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5044961683/10000000000 : ℝ)^8383 ≤ (20219330673421/50000000000000 : ℝ)^6335 := by
    have hnat : (5044961683 : ℕ)^8383*50000000000000^6335 ≤ 20219330673421^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044961683 10000000000 20219330673421 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172533769/400000000 : ℝ), (1842983227/5000000000 : ℝ), (5044961683/10000000000 : ℝ)] ![(32866662435763/100000000000000 : ℝ), (13347338103691/50000000000000 : ℝ), (20219330673421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172533769/400000000 : ℝ)|^8383 ≤ (32866662435763/100000000000000 : ℝ)^6335
        have hw : |(172533769/400000000 : ℝ)|=(172533769/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1842983227/5000000000 : ℝ)|^8383 ≤ (13347338103691/50000000000000 : ℝ)^6335
        have hw : |(1842983227/5000000000 : ℝ)|=(1842983227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5044961683/10000000000 : ℝ)|^8383 ≤ (20219330673421/50000000000000 : ℝ)^6335
        have hw : |(5044961683/10000000000 : ℝ)|=(5044961683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s1_4 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-415728751/2000000000 : ℝ)*x 0 + (2510613407/5000000000 : ℝ)*x 1 + (5679622857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415728751/2000000000 : ℝ)^8383 ≤ (2501841065723/20000000000000 : ℝ)^6335 := by
    have hnat : (415728751 : ℕ)^8383*20000000000000^6335 ≤ 2501841065723^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415728751 2000000000 2501841065723 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2510613407/5000000000 : ℝ)^8383 ≤ (40187097724693/100000000000000 : ℝ)^6335 := by
    have hnat : (2510613407 : ℕ)^8383*100000000000000^6335 ≤ 40187097724693^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510613407 5000000000 40187097724693 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5679622857/10000000000 : ℝ)^8383 ≤ (47303696930961/100000000000000 : ℝ)^6335 := by
    have hnat : (5679622857 : ℕ)^8383*100000000000000^6335 ≤ 47303696930961^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5679622857 10000000000 47303696930961 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415728751/2000000000 : ℝ), (2510613407/5000000000 : ℝ), (5679622857/10000000000 : ℝ)] ![(2501841065723/20000000000000 : ℝ), (40187097724693/100000000000000 : ℝ), (47303696930961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415728751/2000000000 : ℝ)|^8383 ≤ (2501841065723/20000000000000 : ℝ)^6335
        have hw : |(-415728751/2000000000 : ℝ)|=(415728751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2510613407/5000000000 : ℝ)|^8383 ≤ (40187097724693/100000000000000 : ℝ)^6335
        have hw : |(2510613407/5000000000 : ℝ)|=(2510613407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5679622857/10000000000 : ℝ)|^8383 ≤ (47303696930961/100000000000000 : ℝ)^6335
        have hw : |(5679622857/10000000000 : ℝ)|=(5679622857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s1_5 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (327661409/625000000 : ℝ)*x 0 + (-1774744681/10000000000 : ℝ)*x 1 + (5679623513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327661409/625000000 : ℝ)^8383 ≤ (21273989477947/50000000000000 : ℝ)^6335 := by
    have hnat : (327661409 : ℕ)^8383*50000000000000^6335 ≤ 21273989477947^6335*625000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327661409 625000000 21273989477947 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1774744681/10000000000 : ℝ)^8383 ≤ (10148316862897/100000000000000 : ℝ)^6335 := by
    have hnat : (1774744681 : ℕ)^8383*100000000000000^6335 ≤ 10148316862897^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774744681 10000000000 10148316862897 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5679623513/10000000000 : ℝ)^8383 ≤ (47303704160861/100000000000000 : ℝ)^6335 := by
    have hnat : (5679623513 : ℕ)^8383*100000000000000^6335 ≤ 47303704160861^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5679623513 10000000000 47303704160861 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327661409/625000000 : ℝ), (-1774744681/10000000000 : ℝ), (5679623513/10000000000 : ℝ)] ![(21273989477947/50000000000000 : ℝ), (10148316862897/100000000000000 : ℝ), (47303704160861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327661409/625000000 : ℝ)|^8383 ≤ (21273989477947/50000000000000 : ℝ)^6335
        have hw : |(327661409/625000000 : ℝ)|=(327661409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1774744681/10000000000 : ℝ)|^8383 ≤ (10148316862897/100000000000000 : ℝ)^6335
        have hw : |(-1774744681/10000000000 : ℝ)|=(1774744681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5679623513/10000000000 : ℝ)|^8383 ≤ (47303704160861/100000000000000 : ℝ)^6335
        have hw : |(5679623513/10000000000 : ℝ)|=(5679623513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s1_6 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621291201/5000000000 : ℝ)*x 0 + (5679624243/10000000000 : ℝ)*x 1 + (-1774743819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621291201/5000000000 : ℝ)^8383 ≤ (10636994357719/25000000000000 : ℝ)^6335 := by
    have hnat : (2621291201 : ℕ)^8383*25000000000000^6335 ≤ 10636994357719^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621291201 5000000000 10636994357719 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5679624243/10000000000 : ℝ)^8383 ≤ (47303712206329/100000000000000 : ℝ)^6335 := by
    have hnat : (5679624243 : ℕ)^8383*100000000000000^6335 ≤ 47303712206329^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5679624243 10000000000 47303712206329 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1774743819/10000000000 : ℝ)^8383 ≤ (2029662068067/20000000000000 : ℝ)^6335 := by
    have hnat : (1774743819 : ℕ)^8383*20000000000000^6335 ≤ 2029662068067^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774743819 10000000000 2029662068067 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621291201/5000000000 : ℝ), (5679624243/10000000000 : ℝ), (-1774743819/10000000000 : ℝ)] ![(10636994357719/25000000000000 : ℝ), (47303712206329/100000000000000 : ℝ), (2029662068067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621291201/5000000000 : ℝ)|^8383 ≤ (10636994357719/25000000000000 : ℝ)^6335
        have hw : |(2621291201/5000000000 : ℝ)|=(2621291201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5679624243/10000000000 : ℝ)|^8383 ≤ (47303712206329/100000000000000 : ℝ)^6335
        have hw : |(5679624243/10000000000 : ℝ)|=(5679624243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1774743819/10000000000 : ℝ)|^8383 ≤ (2029662068067/20000000000000 : ℝ)^6335
        have hw : |(-1774743819/10000000000 : ℝ)|=(1774743819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s1_7 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1078707961/2500000000 : ℝ)*x 0 + (5026744449/10000000000 : ℝ)*x 1 + (926134247/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078707961/2500000000 : ℝ)^8383 ≤ (32881663091983/100000000000000 : ℝ)^6335 := by
    have hnat : (1078707961 : ℕ)^8383*100000000000000^6335 ≤ 32881663091983^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078707961 2500000000 32881663091983 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5026744449/10000000000 : ℝ)^8383 ≤ (20122772194681/50000000000000 : ℝ)^6335 := by
    have hnat : (5026744449 : ℕ)^8383*50000000000000^6335 ≤ 20122772194681^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026744449 10000000000 20122772194681 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926134247/2500000000 : ℝ)^8383 ≤ (26872792502711/100000000000000 : ℝ)^6335 := by
    have hnat : (926134247 : ℕ)^8383*100000000000000^6335 ≤ 26872792502711^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926134247 2500000000 26872792502711 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078707961/2500000000 : ℝ), (5026744449/10000000000 : ℝ), (926134247/2500000000 : ℝ)] ![(32881663091983/100000000000000 : ℝ), (20122772194681/50000000000000 : ℝ), (26872792502711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078707961/2500000000 : ℝ)|^8383 ≤ (32881663091983/100000000000000 : ℝ)^6335
        have hw : |(1078707961/2500000000 : ℝ)|=(1078707961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5026744449/10000000000 : ℝ)|^8383 ≤ (20122772194681/50000000000000 : ℝ)^6335
        have hw : |(5026744449/10000000000 : ℝ)|=(5026744449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(926134247/2500000000 : ℝ)|^8383 ≤ (26872792502711/100000000000000 : ℝ)^6335
        have hw : |(926134247/2500000000 : ℝ)|=(926134247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1190_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1727/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (609/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2957/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20223/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1727/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (609/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1727/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (609/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1727/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (609/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1727/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (609/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1727/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (609/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1727/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (609/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (609/100000 : ℝ) ^ (4191/1024 : ℝ) ≤ (85692043857/100000000000000000000 : ℝ) := by
    have hpowers : (609/100000 : ℝ)^4191 ≤ (85692043857/100000000000000000000 : ℝ)^1024 := by
      have hnat : (609 : ℕ)^4191*100000000000000000000^1024 ≤ 85692043857^1024*100000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        609 100000 85692043857 100000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (609/100000 : ℝ)) (X := (85692043857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1727/6250 : ℝ) ^ (4191/1024 : ℝ) ≤ (517400902233692853/100000000000000000000 : ℝ) := by
    have hpowers : (1727/6250 : ℝ)^4191 ≤ (517400902233692853/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1727 : ℕ)^4191*100000000000000000000^1024 ≤ 517400902233692853^1024*6250^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1727 6250 517400902233692853 100000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1727/6250 : ℝ)) (X := (517400902233692853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000085692043857/50000000000000000000 : ℝ) ≤ (10000000004187481/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (50000000085692043857/50000000000000000000 : ℝ)^1024 ≤ (10000000004187481/10000000000000000 : ℝ)^4191 := by
      have hnat : (50000000085692043857 : ℕ)^1024*10000000000000000^4191 ≤ 10000000004187481^4191*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000085692043857 50000000000000000000 10000000004187481 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000004187481/10000000000000000 : ℝ)) (X := (50000000085692043857/50000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10051740098792573671/10000000000000000000 : ℝ) ≤ (10012617179357307/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (10051740098792573671/10000000000000000000 : ℝ)^1024 ≤ (10012617179357307/10000000000000000 : ℝ)^4191 := by
      have hnat : (10051740098792573671 : ℕ)^1024*10000000000000000^4191 ≤ 10012617179357307^4191*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10051740098792573671 10000000000000000000 10012617179357307 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012617179357307/10000000000000000 : ℝ)) (X := (10051740098792573671/10000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50517400902233692853/50000000000000000000 : ℝ) ≤ (10025234354527133/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (50517400902233692853/50000000000000000000 : ℝ)^1024 ≤ (10025234354527133/10000000000000000 : ℝ)^4191 := by
      have hnat : (50517400902233692853 : ℕ)^1024*10000000000000000^4191 ≤ 10025234354527133^4191*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50517400902233692853 50000000000000000000 10025234354527133 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025234354527133/10000000000000000 : ℝ)) (X := (50517400902233692853/50000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(85692043857/100000000000000000000 : ℝ) ≤ ((54042926478760290199/54046000000000000000 : ℝ)+2*(6308587584913/1351150000000000 : ℝ)*(609/100000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (54042926478760290199/54046000000000000000 : ℝ)+2*(6308587584913/1351150000000000 : ℝ)*(609/100000 : ℝ)=(10000000004187481/10000000000000000 : ℝ) by norm_num, show 1+2*(85692043857/100000000000000000000 : ℝ)=(50000000085692043857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(517400902233692853/100000000000000000000 : ℝ)+(85692043857/100000000000000000000 : ℝ) ≤ ((54042926478760290199/54046000000000000000 : ℝ)+(6308587584913/1351150000000000 : ℝ)*((1727/6250 : ℝ)+(609/100000 : ℝ)))^(4191/1024 : ℝ) := by
    rw [show (54042926478760290199/54046000000000000000 : ℝ)+(6308587584913/1351150000000000 : ℝ)*((1727/6250 : ℝ)+(609/100000 : ℝ))=(10012617179357307/10000000000000000 : ℝ) by norm_num, show 1+(517400902233692853/100000000000000000000 : ℝ)+(85692043857/100000000000000000000 : ℝ)=(10051740098792573671/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(517400902233692853/100000000000000000000 : ℝ) ≤ ((54042926478760290199/54046000000000000000 : ℝ)+2*(6308587584913/1351150000000000 : ℝ)*(1727/6250 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (54042926478760290199/54046000000000000000 : ℝ)+2*(6308587584913/1351150000000000 : ℝ)*(1727/6250 : ℝ)=(10025234354527133/10000000000000000 : ℝ) by norm_num, show 1+2*(517400902233692853/100000000000000000000 : ℝ)=(50517400902233692853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54042926478760290199/54046000000000000000 : ℝ)*(X 1 0+X 2 0)+(6308587584913/1351150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (609/100000 : ℝ)) (hi := (1727/6250 : ℝ)) (c := (54042926478760290199/54046000000000000000 : ℝ)) (alpha := (6308587584913/1351150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54042926478760290199/54046000000000000000 : ℝ)*(X 0 1+X 2 1)+(6308587584913/1351150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (609/100000 : ℝ)) (hi := (1727/6250 : ℝ)) (c := (54042926478760290199/54046000000000000000 : ℝ)) (alpha := (6308587584913/1351150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54042926478760290199/54046000000000000000 : ℝ)*(X 0 2+X 1 2)+(6308587584913/1351150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (609/100000 : ℝ)) (hi := (1727/6250 : ℝ)) (c := (54042926478760290199/54046000000000000000 : ℝ)) (alpha := (6308587584913/1351150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2077902333/10000000000 : ℝ)*X 0 0+(5688870823/10000000000 : ℝ)*X 0 1+(2506077663/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5416491791/10000000000 : ℝ)*X 1 0+(-305276547/1250000000 : ℝ)*X 1 1+(1002431123/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2708245433/5000000000 : ℝ)*X 2 0+(78314941/156250000 : ℝ)*X 2 1+(-488442561/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172533769/400000000 : ℝ)*X 0 0+(1842983227/5000000000 : ℝ)*X 0 1+(5044961683/10000000000 : ℝ)*X 0 2+(172533769/400000000 : ℝ)*X 1 0+(1842983227/5000000000 : ℝ)*X 1 1+(5044961683/10000000000 : ℝ)*X 1 2+(172533769/400000000 : ℝ)*X 2 0+(1842983227/5000000000 : ℝ)*X 2 1+(5044961683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-415728751/2000000000 : ℝ)*X 0 0+(2510613407/5000000000 : ℝ)*X 0 1+(5679622857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((327661409/625000000 : ℝ)*X 1 0+(-1774744681/10000000000 : ℝ)*X 1 1+(5679623513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2621291201/5000000000 : ℝ)*X 2 0+(5679624243/10000000000 : ℝ)*X 2 1+(-1774743819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1078707961/2500000000 : ℝ)*X 0 0+(5026744449/10000000000 : ℝ)*X 0 1+(926134247/2500000000 : ℝ)*X 0 2+(1078707961/2500000000 : ℝ)*X 1 0+(5026744449/10000000000 : ℝ)*X 1 1+(926134247/2500000000 : ℝ)*X 1 2+(1078707961/2500000000 : ℝ)*X 2 0+(5026744449/10000000000 : ℝ)*X 2 1+(926134247/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12216303340495248875996843097/2702300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (148919221/12500000000000 : ℝ)*(base19) + (114948673/12500000000000 : ℝ)*(base23) + (62357117/25000000000000 : ℝ)*(upper3) + (420403/4000000000000 : ℝ)*(upper4) + (11175331/100000000000000 : ℝ)*(upper5) + (1106792697617499/100000000000000 : ℝ)*(major0) + (1106792697617499/100000000000000 : ℝ)*(major1) + (1106792697617499/100000000000000 : ℝ)*(major2) + (738867185540341/50000000000000 : ℝ)*(sp0) + (73886949267839/5000000000000 : ℝ)*(sp1) + (369434814280291/25000000000000 : ℝ)*(sp2) + (14716819144737/2000000000000 : ℝ)*(sp3) + (2902814933/50000000000000 : ℝ)*(sp4) + (4110597403/100000000000000 : ℝ)*(sp7) + (735845067834253/100000000000000 : ℝ)*(f.failure) + (369435044177637/25000000000000 : ℝ)*(f.sum) + (34343835971529/33778750000000000000000000000 : ℝ)*base66 + (16476857442381872301/5404600000000000000000000000000000 : ℝ)*base67 + (14164466088687272301/5404600000000000000000000000000000 : ℝ)*base69 + (9047562122621127699/5404600000000000000000000000000000 : ℝ)*base72 + (568761031384969/135115000000000000000000000000 : ℝ)*base73 + (9960442819339672301/5404600000000000000000000000000000 : ℝ)*base75 + (33188873202576472301/5404600000000000000000000000000000 : ℝ)*base77 + (17775100558037727699/5404600000000000000000000000000000 : ℝ)*base80 + (24188615447591/33778750000000000000000000000 : ℝ)*base81 + (10115913/2000000000000000000000 : ℝ)*base89 + (10115913/2000000000000000000000 : ℝ)*base91 + (10115913/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5029127649506613260127073257/1351150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1409558693/100000000000000 : ℝ)*(base19) + (42671571/2500000000000 : ℝ)*(base23) + (117293727/100000000000000 : ℝ)*(upper2) + (14901751/6250000000000 : ℝ)*(upper3) + (140276347/100000000000000 : ℝ)*(upper5) + (568788129633927/50000000000000 : ℝ)*(major0) + (568788129633927/50000000000000 : ℝ)*(major1) + (568788129633927/50000000000000 : ℝ)*(major2) + (7044389421/100000000000000 : ℝ)*(sp1) + (525122201/5000000000000 : ℝ)*(sp2) + (759420522069003/50000000000000 : ℝ)*(sp4) + (379708147547473/25000000000000 : ℝ)*(sp5) + (303765766966229/20000000000000 : ℝ)*(sp6) + (378155675163697/50000000000000 : ℝ)*(sp7) + (378155675163697/50000000000000 : ℝ)*(f.failure) + (759420522069003/50000000000000 : ℝ)*(f.sum) + (29977383333643/67557500000000000000000000000 : ℝ)*base66 + (30866290611326978527/2702300000000000000000000000000000 : ℝ)*base68 + (16230697650462178527/2702300000000000000000000000000000 : ℝ)*base70 + (28830631821038478527/2702300000000000000000000000000000 : ℝ)*base72 + (20095212035117/67557500000000000000000000000 : ℝ)*base73 + (15446696562410878527/2702300000000000000000000000000000 : ℝ)*base76 + (16742280148445778527/2702300000000000000000000000000000 : ℝ)*base78 + (11313355327438278527/2702300000000000000000000000000000 : ℝ)*base80 + (329332030280449/135115000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4331037/1000000000000000000000 : ℝ)*base89 + (4331037/1000000000000000000000 : ℝ)*base91 + (4331037/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1190_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1727/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (609/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2957/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20223/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1190_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1190_s2_0 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064297981/5000000000 : ℝ)*x 0 + (1375477543/2500000000 : ℝ)*x 1 + (645854447/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064297981/5000000000 : ℝ)^8383 ≤ (3227133820277/25000000000000 : ℝ)^6335 := by
    have hnat : (1064297981 : ℕ)^8383*25000000000000^6335 ≤ 3227133820277^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064297981 5000000000 3227133820277 25000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375477543/2500000000 : ℝ)^8383 ≤ (22677534395391/50000000000000 : ℝ)^6335 := by
    have hnat : (1375477543 : ℕ)^8383*50000000000000^6335 ≤ 22677534395391^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375477543 2500000000 22677534395391 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (645854447/1250000000 : ℝ)^8383 ≤ (5217049490193/12500000000000 : ℝ)^6335 := by
    have hnat : (645854447 : ℕ)^8383*12500000000000^6335 ≤ 5217049490193^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645854447 1250000000 5217049490193 12500000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064297981/5000000000 : ℝ), (1375477543/2500000000 : ℝ), (645854447/1250000000 : ℝ)] ![(3227133820277/25000000000000 : ℝ), (22677534395391/50000000000000 : ℝ), (5217049490193/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064297981/5000000000 : ℝ)|^8383 ≤ (3227133820277/25000000000000 : ℝ)^6335
        have hw : |(-1064297981/5000000000 : ℝ)|=(1064297981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375477543/2500000000 : ℝ)|^8383 ≤ (22677534395391/50000000000000 : ℝ)^6335
        have hw : |(1375477543/2500000000 : ℝ)|=(1375477543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(645854447/1250000000 : ℝ)|^8383 ≤ (5217049490193/12500000000000 : ℝ)^6335
        have hw : |(645854447/1250000000 : ℝ)|=(645854447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s2_1 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5371827617/10000000000 : ℝ)*x 0 + (-1151241327/5000000000 : ℝ)*x 1 + (5166839573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371827617/10000000000 : ℝ)^8383 ≤ (43941515021249/100000000000000 : ℝ)^6335 := by
    have hnat : (5371827617 : ℕ)^8383*100000000000000^6335 ≤ 43941515021249^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371827617 10000000000 43941515021249 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1151241327/5000000000 : ℝ)^8383 ≤ (14322046328143/100000000000000 : ℝ)^6335 := by
    have hnat : (1151241327 : ℕ)^8383*100000000000000^6335 ≤ 14322046328143^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151241327 5000000000 14322046328143 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5166839573/10000000000 : ℝ)^8383 ≤ (130426370769/312500000000 : ℝ)^6335 := by
    have hnat : (5166839573 : ℕ)^8383*312500000000^6335 ≤ 130426370769^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166839573 10000000000 130426370769 312500000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371827617/10000000000 : ℝ), (-1151241327/5000000000 : ℝ), (5166839573/10000000000 : ℝ)] ![(43941515021249/100000000000000 : ℝ), (14322046328143/100000000000000 : ℝ), (130426370769/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371827617/10000000000 : ℝ)|^8383 ≤ (43941515021249/100000000000000 : ℝ)^6335
        have hw : |(5371827617/10000000000 : ℝ)|=(5371827617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1151241327/5000000000 : ℝ)|^8383 ≤ (14322046328143/100000000000000 : ℝ)^6335
        have hw : |(-1151241327/5000000000 : ℝ)|=(1151241327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5166839573/10000000000 : ℝ)|^8383 ≤ (130426370769/312500000000 : ℝ)^6335
        have hw : |(5166839573/10000000000 : ℝ)|=(5166839573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s2_2 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5371829197/10000000000 : ℝ)*x 0 + (1291709337/2500000000 : ℝ)*x 1 + (-460496693/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371829197/10000000000 : ℝ)^8383 ≤ (43941532123879/100000000000000 : ℝ)^6335 := by
    have hnat : (5371829197 : ℕ)^8383*100000000000000^6335 ≤ 43941532123879^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371829197 10000000000 43941532123879 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291709337/2500000000 : ℝ)^8383 ≤ (20868207431359/50000000000000 : ℝ)^6335 := by
    have hnat : (1291709337 : ℕ)^8383*50000000000000^6335 ≤ 20868207431359^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291709337 2500000000 20868207431359 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460496693/2000000000 : ℝ)^8383 ≤ (7161026501811/50000000000000 : ℝ)^6335 := by
    have hnat : (460496693 : ℕ)^8383*50000000000000^6335 ≤ 7161026501811^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460496693 2000000000 7161026501811 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371829197/10000000000 : ℝ), (1291709337/2500000000 : ℝ), (-460496693/2000000000 : ℝ)] ![(43941532123879/100000000000000 : ℝ), (20868207431359/50000000000000 : ℝ), (7161026501811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371829197/10000000000 : ℝ)|^8383 ≤ (43941532123879/100000000000000 : ℝ)^6335
        have hw : |(5371829197/10000000000 : ℝ)|=(5371829197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1291709337/2500000000 : ℝ)|^8383 ≤ (20868207431359/50000000000000 : ℝ)^6335
        have hw : |(1291709337/2500000000 : ℝ)|=(1291709337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-460496693/2000000000 : ℝ)|^8383 ≤ (7161026501811/50000000000000 : ℝ)^6335
        have hw : |(-460496693/2000000000 : ℝ)|=(460496693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s2_3 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (17392963/40000000 : ℝ)*x 0 + (4024548959/10000000000 : ℝ)*x 1 + (939489781/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17392963/40000000 : ℝ)^8383 ≤ (1660949355401/5000000000000 : ℝ)^6335 := by
    have hnat : (17392963 : ℕ)^8383*5000000000000^6335 ≤ 1660949355401^6335*40000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17392963 40000000 1660949355401 5000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4024548959/10000000000 : ℝ)^8383 ≤ (2998671371527/10000000000000 : ℝ)^6335 := by
    have hnat : (4024548959 : ℕ)^8383*10000000000000^6335 ≤ 2998671371527^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024548959 10000000000 2998671371527 10000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (939489781/2000000000 : ℝ)^8383 ≤ (36794299161683/100000000000000 : ℝ)^6335 := by
    have hnat : (939489781 : ℕ)^8383*100000000000000^6335 ≤ 36794299161683^6335*2000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939489781 2000000000 36794299161683 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17392963/40000000 : ℝ), (4024548959/10000000000 : ℝ), (939489781/2000000000 : ℝ)] ![(1660949355401/5000000000000 : ℝ), (2998671371527/10000000000000 : ℝ), (36794299161683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17392963/40000000 : ℝ)|^8383 ≤ (1660949355401/5000000000000 : ℝ)^6335
        have hw : |(17392963/40000000 : ℝ)|=(17392963/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4024548959/10000000000 : ℝ)|^8383 ≤ (2998671371527/10000000000000 : ℝ)^6335
        have hw : |(4024548959/10000000000 : ℝ)|=(4024548959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(939489781/2000000000 : ℝ)|^8383 ≤ (36794299161683/100000000000000 : ℝ)^6335
        have hw : |(939489781/2000000000 : ℝ)|=(939489781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s2_4 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-66521409/312500000 : ℝ)*x 0 + (1292267679/2500000000 : ℝ)*x 1 + (1374913527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66521409/312500000 : ℝ)^8383 ≤ (12909250508163/100000000000000 : ℝ)^6335 := by
    have hnat : (66521409 : ℕ)^8383*100000000000000^6335 ≤ 12909250508163^6335*312500000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66521409 312500000 12909250508163 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292267679/2500000000 : ℝ)^8383 ≤ (41760289337521/100000000000000 : ℝ)^6335 := by
    have hnat : (1292267679 : ℕ)^8383*100000000000000^6335 ≤ 41760289337521^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292267679 2500000000 41760289337521 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1374913527/2500000000 : ℝ)^8383 ≤ (181321840559/400000000000 : ℝ)^6335 := by
    have hnat : (1374913527 : ℕ)^8383*400000000000^6335 ≤ 181321840559^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374913527 2500000000 181321840559 400000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66521409/312500000 : ℝ), (1292267679/2500000000 : ℝ), (1374913527/2500000000 : ℝ)] ![(12909250508163/100000000000000 : ℝ), (41760289337521/100000000000000 : ℝ), (181321840559/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66521409/312500000 : ℝ)|^8383 ≤ (12909250508163/100000000000000 : ℝ)^6335
        have hw : |(-66521409/312500000 : ℝ)|=(66521409/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292267679/2500000000 : ℝ)|^8383 ≤ (41760289337521/100000000000000 : ℝ)^6335
        have hw : |(1292267679/2500000000 : ℝ)|=(1292267679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1374913527/2500000000 : ℝ)|^8383 ≤ (181321840559/400000000000 : ℝ)^6335
        have hw : |(1374913527/2500000000 : ℝ)|=(1374913527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s2_5 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643271243/5000000000 : ℝ)*x 0 + (-123104159/625000000 : ℝ)*x 1 + (5499654121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643271243/5000000000 : ℝ)^8383 ≤ (43020728097989/100000000000000 : ℝ)^6335 := by
    have hnat : (2643271243 : ℕ)^8383*100000000000000^6335 ≤ 43020728097989^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643271243 5000000000 43020728097989 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123104159/625000000 : ℝ)^8383 ≤ (1164881160753/10000000000000 : ℝ)^6335 := by
    have hnat : (123104159 : ℕ)^8383*10000000000000^6335 ≤ 1164881160753^6335*625000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123104159 625000000 1164881160753 10000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5499654121/10000000000 : ℝ)^8383 ≤ (22665230140771/50000000000000 : ℝ)^6335 := by
    have hnat : (5499654121 : ℕ)^8383*50000000000000^6335 ≤ 22665230140771^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499654121 10000000000 22665230140771 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643271243/5000000000 : ℝ), (-123104159/625000000 : ℝ), (5499654121/10000000000 : ℝ)] ![(43020728097989/100000000000000 : ℝ), (1164881160753/10000000000000 : ℝ), (22665230140771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643271243/5000000000 : ℝ)|^8383 ≤ (43020728097989/100000000000000 : ℝ)^6335
        have hw : |(2643271243/5000000000 : ℝ)|=(2643271243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123104159/625000000 : ℝ)|^8383 ≤ (1164881160753/10000000000000 : ℝ)^6335
        have hw : |(-123104159/625000000 : ℝ)|=(123104159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5499654121/10000000000 : ℝ)|^8383 ≤ (22665230140771/50000000000000 : ℝ)^6335
        have hw : |(5499654121/10000000000 : ℝ)|=(5499654121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s2_6 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660817831/1250000000 : ℝ)*x 0 + (549965413/1000000000 : ℝ)*x 1 + (-492416577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660817831/1250000000 : ℝ)^8383 ≤ (43020729842501/100000000000000 : ℝ)^6335 := by
    have hnat : (660817831 : ℕ)^8383*100000000000000^6335 ≤ 43020729842501^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660817831 1250000000 43020729842501 100000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549965413/1000000000 : ℝ)^8383 ≤ (9066092075941/20000000000000 : ℝ)^6335 := by
    have hnat : (549965413 : ℕ)^8383*20000000000000^6335 ≤ 9066092075941^6335*1000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549965413 1000000000 9066092075941 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492416577/2500000000 : ℝ)^8383 ≤ (5824404880293/50000000000000 : ℝ)^6335 := by
    have hnat : (492416577 : ℕ)^8383*50000000000000^6335 ≤ 5824404880293^6335*2500000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492416577 2500000000 5824404880293 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660817831/1250000000 : ℝ), (549965413/1000000000 : ℝ), (-492416577/2500000000 : ℝ)] ![(43020729842501/100000000000000 : ℝ), (9066092075941/20000000000000 : ℝ), (5824404880293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660817831/1250000000 : ℝ)|^8383 ≤ (43020729842501/100000000000000 : ℝ)^6335
        have hw : |(660817831/1250000000 : ℝ)|=(660817831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549965413/1000000000 : ℝ)|^8383 ≤ (9066092075941/20000000000000 : ℝ)^6335
        have hw : |(549965413/1000000000 : ℝ)|=(549965413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492416577/2500000000 : ℝ)|^8383 ≤ (5824404880293/50000000000000 : ℝ)^6335
        have hw : |(-492416577/2500000000 : ℝ)|=(492416577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1190_s2_7 (p : ℝ) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543552737/1250000000 : ℝ)*x 0 + (4692962931/10000000000 : ℝ)*x 1 + (2014538781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543552737/1250000000 : ℝ)^8383 ≤ (6644163679773/20000000000000 : ℝ)^6335 := by
    have hnat : (543552737 : ℕ)^8383*20000000000000^6335 ≤ 6644163679773^6335*1250000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543552737 1250000000 6644163679773 20000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4692962931/10000000000 : ℝ)^8383 ≤ (3674780900499/10000000000000 : ℝ)^6335 := by
    have hnat : (4692962931 : ℕ)^8383*10000000000000^6335 ≤ 3674780900499^6335*10000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4692962931 10000000000 3674780900499 10000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014538781/5000000000 : ℝ)^8383 ≤ (15015686292143/50000000000000 : ℝ)^6335 := by
    have hnat : (2014538781 : ℕ)^8383*50000000000000^6335 ≤ 15015686292143^6335*5000000000^8383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014538781 5000000000 15015686292143 50000000000000 8383 6335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8383/2048 : ℝ)) 8383 6335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543552737/1250000000 : ℝ), (4692962931/10000000000 : ℝ), (2014538781/5000000000 : ℝ)] ![(6644163679773/20000000000000 : ℝ), (3674780900499/10000000000000 : ℝ), (15015686292143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543552737/1250000000 : ℝ)|^8383 ≤ (6644163679773/20000000000000 : ℝ)^6335
        have hw : |(543552737/1250000000 : ℝ)|=(543552737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4692962931/10000000000 : ℝ)|^8383 ≤ (3674780900499/10000000000000 : ℝ)^6335
        have hw : |(4692962931/10000000000 : ℝ)|=(4692962931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014538781/5000000000 : ℝ)|^8383 ≤ (15015686292143/50000000000000 : ℝ)^6335
        have hw : |(2014538781/5000000000 : ℝ)|=(2014538781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1190_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20223/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2957/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4641/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4091/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20223/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2957/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20223/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2957/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20223/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2957/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20223/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2957/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20223/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2957/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20223/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2957/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2957/50000 : ℝ) ^ (4191/1024 : ℝ) ≤ (470498771192541/50000000000000000000 : ℝ) := by
    have hpowers : (2957/50000 : ℝ)^4191 ≤ (470498771192541/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2957 : ℕ)^4191*50000000000000000000^1024 ≤ 470498771192541^1024*50000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2957 50000 470498771192541 50000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2957/50000 : ℝ)) (X := (470498771192541/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20223/100000 : ℝ) ^ (4191/1024 : ℝ) ≤ (28841193717284093/20000000000000000000 : ℝ) := by
    have hpowers : (20223/100000 : ℝ)^4191 ≤ (28841193717284093/20000000000000000000 : ℝ)^1024 := by
      have hnat : (20223 : ℕ)^4191*20000000000000000000^1024 ≤ 28841193717284093^1024*100000^4191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20223 100000 28841193717284093 20000000000000000000 4191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20223/100000 : ℝ)) (X := (28841193717284093/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000470498771192541/25000000000000000000 : ℝ) ≤ (10000045983041357/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (25000470498771192541/25000000000000000000 : ℝ)^1024 ≤ (10000045983041357/10000000000000000 : ℝ)^4191 := by
      have hnat : (25000470498771192541 : ℕ)^1024*10000000000000000^4191 ≤ 10000045983041357^4191*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000470498771192541 25000000000000000000 10000045983041357 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000045983041357/10000000000000000 : ℝ)) (X := (25000470498771192541/25000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100145146966128805547/100000000000000000000 : ℝ) ≤ (10003544477486809/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (100145146966128805547/100000000000000000000 : ℝ)^1024 ≤ (10003544477486809/10000000000000000 : ℝ)^4191 := by
      have hnat : (100145146966128805547 : ℕ)^1024*10000000000000000^4191 ≤ 10003544477486809^4191*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100145146966128805547 100000000000000000000 10003544477486809 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003544477486809/10000000000000000 : ℝ)) (X := (100145146966128805547/100000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10028841193717284093/10000000000000000000 : ℝ) ≤ (10007042971932261/10000000000000000 : ℝ) ^ (4191/1024 : ℝ) := by
    have hpowers : (10028841193717284093/10000000000000000000 : ℝ)^1024 ≤ (10007042971932261/10000000000000000 : ℝ)^4191 := by
      have hnat : (10028841193717284093 : ℕ)^1024*10000000000000000^4191 ≤ 10007042971932261^4191*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10028841193717284093 10000000000000000000 10007042971932261 10000000000000000 1024 4191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007042971932261/10000000000000000 : ℝ)) (X := (10028841193717284093/10000000000000000000 : ℝ)) (by norm_num) 4191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(470498771192541/50000000000000000000 : ℝ) ≤ ((143049277779037971057/143090000000000000000 : ℝ)+2*(874623611363/357725000000000 : ℝ)*(2957/50000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (143049277779037971057/143090000000000000000 : ℝ)+2*(874623611363/357725000000000 : ℝ)*(2957/50000 : ℝ)=(10000045983041357/10000000000000000 : ℝ) by norm_num, show 1+2*(470498771192541/50000000000000000000 : ℝ)=(25000470498771192541/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28841193717284093/20000000000000000000 : ℝ)+(470498771192541/50000000000000000000 : ℝ) ≤ ((143049277779037971057/143090000000000000000 : ℝ)+(874623611363/357725000000000 : ℝ)*((20223/100000 : ℝ)+(2957/50000 : ℝ)))^(4191/1024 : ℝ) := by
    rw [show (143049277779037971057/143090000000000000000 : ℝ)+(874623611363/357725000000000 : ℝ)*((20223/100000 : ℝ)+(2957/50000 : ℝ))=(10003544477486809/10000000000000000 : ℝ) by norm_num, show 1+(28841193717284093/20000000000000000000 : ℝ)+(470498771192541/50000000000000000000 : ℝ)=(100145146966128805547/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28841193717284093/20000000000000000000 : ℝ) ≤ ((143049277779037971057/143090000000000000000 : ℝ)+2*(874623611363/357725000000000 : ℝ)*(20223/100000 : ℝ))^(4191/1024 : ℝ) := by
    rw [show (143049277779037971057/143090000000000000000 : ℝ)+2*(874623611363/357725000000000 : ℝ)*(20223/100000 : ℝ)=(10007042971932261/10000000000000000 : ℝ) by norm_num, show 1+2*(28841193717284093/20000000000000000000 : ℝ)=(10028841193717284093/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (143049277779037971057/143090000000000000000 : ℝ)*(X 1 0+X 2 0)+(874623611363/357725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (2957/50000 : ℝ)) (hi := (20223/100000 : ℝ)) (c := (143049277779037971057/143090000000000000000 : ℝ)) (alpha := (874623611363/357725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (143049277779037971057/143090000000000000000 : ℝ)*(X 0 1+X 2 1)+(874623611363/357725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (2957/50000 : ℝ)) (hi := (20223/100000 : ℝ)) (c := (143049277779037971057/143090000000000000000 : ℝ)) (alpha := (874623611363/357725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (143049277779037971057/143090000000000000000 : ℝ)*(X 0 2+X 1 2)+(874623611363/357725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4191/1024 : ℝ)) (lo := (2957/50000 : ℝ)) (hi := (20223/100000 : ℝ)) (c := (143049277779037971057/143090000000000000000 : ℝ)) (alpha := (874623611363/357725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1064297981/5000000000 : ℝ)*X 0 0+(1375477543/2500000000 : ℝ)*X 0 1+(645854447/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5371827617/10000000000 : ℝ)*X 1 0+(-1151241327/5000000000 : ℝ)*X 1 1+(5166839573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5371829197/10000000000 : ℝ)*X 2 0+(1291709337/2500000000 : ℝ)*X 2 1+(-460496693/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((17392963/40000000 : ℝ)*X 0 0+(4024548959/10000000000 : ℝ)*X 0 1+(939489781/2000000000 : ℝ)*X 0 2+(17392963/40000000 : ℝ)*X 1 0+(4024548959/10000000000 : ℝ)*X 1 1+(939489781/2000000000 : ℝ)*X 1 2+(17392963/40000000 : ℝ)*X 2 0+(4024548959/10000000000 : ℝ)*X 2 1+(939489781/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-66521409/312500000 : ℝ)*X 0 0+(1292267679/2500000000 : ℝ)*X 0 1+(1374913527/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643271243/5000000000 : ℝ)*X 1 0+(-123104159/625000000 : ℝ)*X 1 1+(5499654121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660817831/1250000000 : ℝ)*X 2 0+(549965413/1000000000 : ℝ)*X 2 1+(-492416577/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543552737/1250000000 : ℝ)*X 0 0+(4692962931/10000000000 : ℝ)*X 0 1+(2014538781/5000000000 : ℝ)*X 0 2+(543552737/1250000000 : ℝ)*X 1 0+(4692962931/10000000000 : ℝ)*X 1 1+(2014538781/5000000000 : ℝ)*X 1 2+(543552737/1250000000 : ℝ)*X 2 0+(4692962931/10000000000 : ℝ)*X 2 1+(2014538781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1190_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38523857429088023093038146819/7154500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (557027393/100000000000000 : ℝ)*(base19) + (629072351/50000000000000 : ℝ)*(base23) + (123275359/100000000000000 : ℝ)*(upper2) + (484598361/100000000000000 : ℝ)*(upper3) + (218193789/100000000000000 : ℝ)*(upper4) + (2235300248167311/100000000000000 : ℝ)*(major0) + (2235300248167311/100000000000000 : ℝ)*(major1) + (2235300248167311/100000000000000 : ℝ)*(major2) + (59688876184247/2000000000000 : ℝ)*(sp0) + (46632384734699/1562500000000 : ℝ)*(sp1) + (746117980475857/25000000000000 : ℝ)*(sp2) + (1486112990932093/100000000000000 : ℝ)*(sp3) + (1468541789/5000000000000 : ℝ)*(sp4) + (14145868951/100000000000000 : ℝ)*(sp7) + (1486127136801043/100000000000000 : ℝ)*(f.failure) + (298447318004813/10000000000000 : ℝ)*(f.sum) + (112824050963599/35772500000000000000000000000 : ℝ)*base66 + (1801684546436717727/14309000000000000000000000000000000 : ℝ)*base67 + (19783887566765717727/14309000000000000000000000000000000 : ℝ)*base69 + (151487164684046717727/14309000000000000000000000000000000 : ℝ)*base71 + (79313968435377/17886250000000000000000000000 : ℝ)*base74 + (160363546827373717727/14309000000000000000000000000000000 : ℝ)*base75 + (116610855423989282273/14309000000000000000000000000000000 : ℝ)*base78 + (4259411305139282273/14309000000000000000000000000000000 : ℝ)*base80 + (97940713423243/71545000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (11443497/2000000000000000000000 : ℝ)*base90 + (11443497/2000000000000000000000 : ℝ)*base92 + (11443497/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7259921007198139742800822533/894312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15058219/781250000000 : ℝ)*(base19) + (2078235777/100000000000000 : ℝ)*(base23) + (839709/50000000000000 : ℝ)*(upper2) + (47668357/20000000000000 : ℝ)*(upper3) + (84563949/50000000000000 : ℝ)*(upper5) + (566404976684877/25000000000000 : ℝ)*(major0) + (566404976684877/25000000000000 : ℝ)*(major1) + (566404976684877/25000000000000 : ℝ)*(major2) + (9509961933/50000000000000 : ℝ)*(sp1) + (2802911059/12500000000000 : ℝ)*(sp2) + (1512477273505773/50000000000000 : ℝ)*(sp4) + (47264587494307/1562500000000 : ℝ)*(sp5) + (47264531960739/1562500000000 : ℝ)*(sp6) + (1506284995871487/100000000000000 : ℝ)*(sp7) + (1506284995871487/100000000000000 : ℝ)*(f.failure) + (1512477273505773/50000000000000 : ℝ)*(f.sum) + (10576672539633/8943125000000000000000000000 : ℝ)*base66 + (7183789156101754989/3577250000000000000000000000000000 : ℝ)*base67 + (23575570246686504989/3577250000000000000000000000000000 : ℝ)*base69 + (381351488178495011/3577250000000000000000000000000000 : ℝ)*base72 + (96322907527671/71545000000000000000000000000 : ℝ)*base73 + (9855658691106004989/3577250000000000000000000000000000 : ℝ)*base75 + (24655933794952004989/3577250000000000000000000000000000 : ℝ)*base77 + (8350338251051754989/3577250000000000000000000000000000 : ℝ)*base79 + (26015824953273/35772500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (467373/2000000000000000000000 : ℝ)*base90 + (467373/2000000000000000000000 : ℝ)*base92 + (467373/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1190_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20223/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2957/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1190_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1190_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1190_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1190_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1190_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4191/1024 : ℝ) ≤ p) (hpb : p ≤ (8383/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30082221/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1190_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

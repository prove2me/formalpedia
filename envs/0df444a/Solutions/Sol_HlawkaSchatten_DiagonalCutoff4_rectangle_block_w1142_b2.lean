-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1142_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:31:51.658179+00:00
-- url     : https://prove2.me/submissions/c3cd9b99-b9aa-462c-8167-0d388574c144

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
theorem support_rectangle_w1142_s6_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166855593/10000000000 : ℝ)*x 0 + (2696691693/5000000000 : ℝ)*x 1 + (5265410079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166855593/10000000000 : ℝ)^8335 ≤ (6583328951697/50000000000000 : ℝ)^6287 := by
    have hnat : (2166855593 : ℕ)^8335*50000000000000^6287 ≤ 6583328951697^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166855593 10000000000 6583328951697 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696691693/5000000000 : ℝ)^8335 ≤ (44107728570259/100000000000000 : ℝ)^6287 := by
    have hnat : (2696691693 : ℕ)^8335*100000000000000^6287 ≤ 44107728570259^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696691693 5000000000 44107728570259 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265410079/10000000000 : ℝ)^8335 ≤ (2670350844993/6250000000000 : ℝ)^6287 := by
    have hnat : (5265410079 : ℕ)^8335*6250000000000^6287 ≤ 2670350844993^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265410079 10000000000 2670350844993 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166855593/10000000000 : ℝ), (2696691693/5000000000 : ℝ), (5265410079/10000000000 : ℝ)] ![(6583328951697/50000000000000 : ℝ), (44107728570259/100000000000000 : ℝ), (2670350844993/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166855593/10000000000 : ℝ)|^8335 ≤ (6583328951697/50000000000000 : ℝ)^6287
        have hw : |(-2166855593/10000000000 : ℝ)|=(2166855593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696691693/5000000000 : ℝ)|^8335 ≤ (44107728570259/100000000000000 : ℝ)^6287
        have hw : |(2696691693/5000000000 : ℝ)|=(2696691693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265410079/10000000000 : ℝ)|^8335 ≤ (2670350844993/6250000000000 : ℝ)^6287
        have hw : |(5265410079/10000000000 : ℝ)|=(5265410079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s6_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344845979/10000000000 : ℝ)*x 0 + (-2231770747/10000000000 : ℝ)*x 1 + (2632705039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344845979/10000000000 : ℝ)^8335 ≤ (43582251500207/100000000000000 : ℝ)^6287 := by
    have hnat : (5344845979 : ℕ)^8335*100000000000000^6287 ≤ 43582251500207^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344845979 10000000000 43582251500207 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2231770747/10000000000 : ℝ)^8335 ≤ (6846067485349/50000000000000 : ℝ)^6287 := by
    have hnat : (2231770747 : ℕ)^8335*50000000000000^6287 ≤ 6846067485349^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231770747 10000000000 6846067485349 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632705039/5000000000 : ℝ)^8335 ≤ (42725613509131/100000000000000 : ℝ)^6287 := by
    have hnat : (2632705039 : ℕ)^8335*100000000000000^6287 ≤ 42725613509131^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632705039 5000000000 42725613509131 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344845979/10000000000 : ℝ), (-2231770747/10000000000 : ℝ), (2632705039/5000000000 : ℝ)] ![(43582251500207/100000000000000 : ℝ), (6846067485349/50000000000000 : ℝ), (42725613509131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344845979/10000000000 : ℝ)|^8335 ≤ (43582251500207/100000000000000 : ℝ)^6287
        have hw : |(5344845979/10000000000 : ℝ)|=(5344845979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2231770747/10000000000 : ℝ)|^8335 ≤ (6846067485349/50000000000000 : ℝ)^6287
        have hw : |(-2231770747/10000000000 : ℝ)|=(2231770747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632705039/5000000000 : ℝ)|^8335 ≤ (42725613509131/100000000000000 : ℝ)^6287
        have hw : |(2632705039/5000000000 : ℝ)|=(2632705039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s6_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344845957/10000000000 : ℝ)*x 0 + (329088131/625000000 : ℝ)*x 1 + (-2231770753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344845957/10000000000 : ℝ)^8335 ≤ (43582251262381/100000000000000 : ℝ)^6287 := by
    have hnat : (5344845957 : ℕ)^8335*100000000000000^6287 ≤ 43582251262381^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344845957 10000000000 43582251262381 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329088131/625000000 : ℝ)^8335 ≤ (42725613702769/100000000000000 : ℝ)^6287 := by
    have hnat : (329088131 : ℕ)^8335*100000000000000^6287 ≤ 42725613702769^6287*625000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329088131 625000000 42725613702769 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231770753/10000000000 : ℝ)^8335 ≤ (27384270039/200000000000 : ℝ)^6287 := by
    have hnat : (2231770753 : ℕ)^8335*200000000000^6287 ≤ 27384270039^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231770753 10000000000 27384270039 200000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344845957/10000000000 : ℝ), (329088131/625000000 : ℝ), (-2231770753/10000000000 : ℝ)] ![(43582251262381/100000000000000 : ℝ), (42725613702769/100000000000000 : ℝ), (27384270039/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344845957/10000000000 : ℝ)|^8335 ≤ (43582251262381/100000000000000 : ℝ)^6287
        have hw : |(5344845957/10000000000 : ℝ)|=(5344845957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329088131/625000000 : ℝ)|^8335 ≤ (42725613702769/100000000000000 : ℝ)^6287
        have hw : |(329088131/625000000 : ℝ)|=(329088131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2231770753/10000000000 : ℝ)|^8335 ≤ (27384270039/200000000000 : ℝ)^6287
        have hw : |(-2231770753/10000000000 : ℝ)|=(2231770753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s6_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364655839/10000000000 : ℝ)*x 0 + (169568133/400000000 : ℝ)*x 1 + (4493802897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364655839/10000000000 : ℝ)^8335 ≤ (33316790663679/100000000000000 : ℝ)^6287 := by
    have hnat : (4364655839 : ℕ)^8335*100000000000000^6287 ≤ 33316790663679^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364655839 10000000000 33316790663679 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169568133/400000000 : ℝ)^8335 ≤ (32053208801253/100000000000000 : ℝ)^6287 := by
    have hnat : (169568133 : ℕ)^8335*100000000000000^6287 ≤ 32053208801253^6287*400000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169568133 400000000 32053208801253 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493802897/10000000000 : ℝ)^8335 ≤ (541093758191/1562500000000 : ℝ)^6287 := by
    have hnat : (4493802897 : ℕ)^8335*1562500000000^6287 ≤ 541093758191^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493802897 10000000000 541093758191 1562500000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364655839/10000000000 : ℝ), (169568133/400000000 : ℝ), (4493802897/10000000000 : ℝ)] ![(33316790663679/100000000000000 : ℝ), (32053208801253/100000000000000 : ℝ), (541093758191/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364655839/10000000000 : ℝ)|^8335 ≤ (33316790663679/100000000000000 : ℝ)^6287
        have hw : |(4364655839/10000000000 : ℝ)|=(4364655839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169568133/400000000 : ℝ)|^8335 ≤ (32053208801253/100000000000000 : ℝ)^6287
        have hw : |(169568133/400000000 : ℝ)|=(169568133/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493802897/10000000000 : ℝ)|^8335 ≤ (541093758191/1562500000000 : ℝ)^6287
        have hw : |(4493802897/10000000000 : ℝ)|=(4493802897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s6_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166860591/10000000000 : ℝ)*x 0 + (2632866629/5000000000 : ℝ)*x 1 + (1078611801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166860591/10000000000 : ℝ)^8335 ≤ (1316669816621/10000000000000 : ℝ)^6287 := by
    have hnat : (2166860591 : ℕ)^8335*10000000000000^6287 ≤ 1316669816621^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166860591 10000000000 1316669816621 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632866629/5000000000 : ℝ)^8335 ≤ (42729090207943/100000000000000 : ℝ)^6287 := by
    have hnat : (2632866629 : ℕ)^8335*100000000000000^6287 ≤ 42729090207943^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632866629 5000000000 42729090207943 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078611801/2000000000 : ℝ)^8335 ≤ (22052105808089/50000000000000 : ℝ)^6287 := by
    have hnat : (1078611801 : ℕ)^8335*50000000000000^6287 ≤ 22052105808089^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078611801 2000000000 22052105808089 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166860591/10000000000 : ℝ), (2632866629/5000000000 : ℝ), (1078611801/2000000000 : ℝ)] ![(1316669816621/10000000000000 : ℝ), (42729090207943/100000000000000 : ℝ), (22052105808089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166860591/10000000000 : ℝ)|^8335 ≤ (1316669816621/10000000000000 : ℝ)^6287
        have hw : |(-2166860591/10000000000 : ℝ)|=(2166860591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632866629/5000000000 : ℝ)|^8335 ≤ (42729090207943/100000000000000 : ℝ)^6287
        have hw : |(2632866629/5000000000 : ℝ)|=(2632866629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078611801/2000000000 : ℝ)|^8335 ≤ (22052105808089/50000000000000 : ℝ)^6287
        have hw : |(1078611801/2000000000 : ℝ)|=(1078611801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s6_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312423397/10000000000 : ℝ)*x 0 + (-1052060951/5000000000 : ℝ)*x 1 + (2696529471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312423397/10000000000 : ℝ)^8335 ≤ (21616050675829/50000000000000 : ℝ)^6287 := by
    have hnat : (5312423397 : ℕ)^8335*50000000000000^6287 ≤ 21616050675829^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312423397 10000000000 21616050675829 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052060951/5000000000 : ℝ)^8335 ≤ (12663687702303/100000000000000 : ℝ)^6287 := by
    have hnat : (1052060951 : ℕ)^8335*100000000000000^6287 ≤ 12663687702303^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052060951 5000000000 12663687702303 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696529471/5000000000 : ℝ)^8335 ≤ (2756513183321/6250000000000 : ℝ)^6287 := by
    have hnat : (2696529471 : ℕ)^8335*6250000000000^6287 ≤ 2756513183321^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696529471 5000000000 2756513183321 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312423397/10000000000 : ℝ), (-1052060951/5000000000 : ℝ), (2696529471/5000000000 : ℝ)] ![(21616050675829/50000000000000 : ℝ), (12663687702303/100000000000000 : ℝ), (2756513183321/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312423397/10000000000 : ℝ)|^8335 ≤ (21616050675829/50000000000000 : ℝ)^6287
        have hw : |(5312423397/10000000000 : ℝ)|=(5312423397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1052060951/5000000000 : ℝ)|^8335 ≤ (12663687702303/100000000000000 : ℝ)^6287
        have hw : |(-1052060951/5000000000 : ℝ)|=(1052060951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696529471/5000000000 : ℝ)|^8335 ≤ (2756513183321/6250000000000 : ℝ)^6287
        have hw : |(2696529471/5000000000 : ℝ)|=(2696529471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s6_6 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312423451/10000000000 : ℝ)*x 0 + (2696529421/5000000000 : ℝ)*x 1 + (-420824393/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312423451/10000000000 : ℝ)^8335 ≤ (2702006370891/6250000000000 : ℝ)^6287 := by
    have hnat : (5312423451 : ℕ)^8335*6250000000000^6287 ≤ 2702006370891^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312423451 10000000000 2702006370891 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696529421/5000000000 : ℝ)^8335 ≤ (22052104924471/50000000000000 : ℝ)^6287 := by
    have hnat : (2696529421 : ℕ)^8335*50000000000000^6287 ≤ 22052104924471^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696529421 5000000000 22052104924471 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420824393/2000000000 : ℝ)^8335 ≤ (1582961025623/12500000000000 : ℝ)^6287 := by
    have hnat : (420824393 : ℕ)^8335*12500000000000^6287 ≤ 1582961025623^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420824393 2000000000 1582961025623 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312423451/10000000000 : ℝ), (2696529421/5000000000 : ℝ), (-420824393/2000000000 : ℝ)] ![(2702006370891/6250000000000 : ℝ), (22052104924471/50000000000000 : ℝ), (1582961025623/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312423451/10000000000 : ℝ)|^8335 ≤ (2702006370891/6250000000000 : ℝ)^6287
        have hw : |(5312423451/10000000000 : ℝ)|=(5312423451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696529421/5000000000 : ℝ)|^8335 ≤ (22052104924471/50000000000000 : ℝ)^6287
        have hw : |(2696529421/5000000000 : ℝ)|=(2696529421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420824393/2000000000 : ℝ)|^8335 ≤ (1582961025623/12500000000000 : ℝ)^6287
        have hw : |(-420824393/2000000000 : ℝ)|=(420824393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s6_7 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872933123/2000000000 : ℝ)*x 0 + (4493159911/10000000000 : ℝ)*x 1 + (529981093/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872933123/2000000000 : ℝ)^8335 ≤ (33316889595647/100000000000000 : ℝ)^6287 := by
    have hnat : (872933123 : ℕ)^8335*100000000000000^6287 ≤ 33316889595647^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872933123 2000000000 33316889595647 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493159911/10000000000 : ℝ)^8335 ≤ (173117158169/500000000000 : ℝ)^6287 := by
    have hnat : (4493159911 : ℕ)^8335*500000000000^6287 ≤ 173117158169^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493159911 10000000000 173117158169 500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529981093/1250000000 : ℝ)^8335 ≤ (4007459845769/12500000000000 : ℝ)^6287 := by
    have hnat : (529981093 : ℕ)^8335*12500000000000^6287 ≤ 4007459845769^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529981093 1250000000 4007459845769 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872933123/2000000000 : ℝ), (4493159911/10000000000 : ℝ), (529981093/1250000000 : ℝ)] ![(33316889595647/100000000000000 : ℝ), (173117158169/500000000000 : ℝ), (4007459845769/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872933123/2000000000 : ℝ)|^8335 ≤ (33316889595647/100000000000000 : ℝ)^6287
        have hw : |(872933123/2000000000 : ℝ)|=(872933123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493159911/10000000000 : ℝ)|^8335 ≤ (173117158169/500000000000 : ℝ)^6287
        have hw : |(4493159911/10000000000 : ℝ)|=(4493159911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529981093/1250000000 : ℝ)|^8335 ≤ (4007459845769/12500000000000 : ℝ)^6287
        have hw : |(529981093/1250000000 : ℝ)|=(529981093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5673/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2263/20000 : ℝ) ^ (4167/1024 : ℝ) ≤ (14092968615199471/100000000000000000000 : ℝ) := by
    have hpowers : (2263/20000 : ℝ)^4167 ≤ (14092968615199471/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2263 : ℕ)^4167*100000000000000000000^1024 ≤ 14092968615199471^1024*20000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2263 20000 14092968615199471 100000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2263/20000 : ℝ)) (X := (14092968615199471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14089/100000 : ℝ) ^ (4167/1024 : ℝ) ≤ (34395963951289691/100000000000000000000 : ℝ) := by
    have hpowers : (14089/100000 : ℝ)^4167 ≤ (34395963951289691/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14089 : ℕ)^4167*100000000000000000000^1024 ≤ 34395963951289691^1024*100000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14089 100000 34395963951289691 100000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14089/100000 : ℝ)) (X := (34395963951289691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014092968615199471/50000000000000000000 : ℝ) ≤ (10000692568567947/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50014092968615199471/50000000000000000000 : ℝ)^1024 ≤ (10000692568567947/10000000000000000 : ℝ)^4167 := by
      have hnat : (50014092968615199471 : ℕ)^1024*10000000000000000^4167 ≤ 10000692568567947^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014092968615199471 50000000000000000000 10000692568567947 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000692568567947/10000000000000000 : ℝ)) (X := (50014092968615199471/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024244466283244581/50000000000000000000 : ℝ) ≤ (10001191350845351/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50024244466283244581/50000000000000000000 : ℝ)^1024 ≤ (10001191350845351/10000000000000000 : ℝ)^4167 := by
      have hnat : (50024244466283244581 : ℕ)^1024*10000000000000000^4167 ≤ 10001191350845351^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024244466283244581 50000000000000000000 10001191350845351 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001191350845351/10000000000000000 : ℝ)) (X := (50024244466283244581/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034395963951289691/50000000000000000000 : ℝ) ≤ (2000338026624551/2000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50034395963951289691/50000000000000000000 : ℝ)^1024 ≤ (2000338026624551/2000000000000000 : ℝ)^4167 := by
      have hnat : (50034395963951289691 : ℕ)^1024*2000000000000000^4167 ≤ 2000338026624551^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034395963951289691 50000000000000000000 2000338026624551 2000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000338026624551/2000000000000000 : ℝ)) (X := (50034395963951289691/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14092968615199471/100000000000000000000 : ℝ) ≤ ((189935847549793373/190000000000000000 : ℝ)+2*(124695569351/69350000000000 : ℝ)*(2263/20000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (189935847549793373/190000000000000000 : ℝ)+2*(124695569351/69350000000000 : ℝ)*(2263/20000 : ℝ)=(10000692568567947/10000000000000000 : ℝ) by norm_num, show 1+2*(14092968615199471/100000000000000000000 : ℝ)=(50014092968615199471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34395963951289691/100000000000000000000 : ℝ)+(14092968615199471/100000000000000000000 : ℝ) ≤ ((189935847549793373/190000000000000000 : ℝ)+(124695569351/69350000000000 : ℝ)*((14089/100000 : ℝ)+(2263/20000 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (189935847549793373/190000000000000000 : ℝ)+(124695569351/69350000000000 : ℝ)*((14089/100000 : ℝ)+(2263/20000 : ℝ))=(10001191350845351/10000000000000000 : ℝ) by norm_num, show 1+(34395963951289691/100000000000000000000 : ℝ)+(14092968615199471/100000000000000000000 : ℝ)=(50024244466283244581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34395963951289691/100000000000000000000 : ℝ) ≤ ((189935847549793373/190000000000000000 : ℝ)+2*(124695569351/69350000000000 : ℝ)*(14089/100000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (189935847549793373/190000000000000000 : ℝ)+2*(124695569351/69350000000000 : ℝ)*(14089/100000 : ℝ)=(2000338026624551/2000000000000000 : ℝ) by norm_num, show 1+2*(34395963951289691/100000000000000000000 : ℝ)=(50034395963951289691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (189935847549793373/190000000000000000 : ℝ)*(X 1 0+X 2 0)+(124695569351/69350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (189935847549793373/190000000000000000 : ℝ)) (alpha := (124695569351/69350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (189935847549793373/190000000000000000 : ℝ)*(X 0 1+X 2 1)+(124695569351/69350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (189935847549793373/190000000000000000 : ℝ)) (alpha := (124695569351/69350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (189935847549793373/190000000000000000 : ℝ)*(X 0 2+X 1 2)+(124695569351/69350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (189935847549793373/190000000000000000 : ℝ)) (alpha := (124695569351/69350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2166855593/10000000000 : ℝ)*X 0 0+(2696691693/5000000000 : ℝ)*X 0 1+(5265410079/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344845979/10000000000 : ℝ)*X 1 0+(-2231770747/10000000000 : ℝ)*X 1 1+(2632705039/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344845957/10000000000 : ℝ)*X 2 0+(329088131/625000000 : ℝ)*X 2 1+(-2231770753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364655839/10000000000 : ℝ)*X 0 0+(169568133/400000000 : ℝ)*X 0 1+(4493802897/10000000000 : ℝ)*X 0 2+(4364655839/10000000000 : ℝ)*X 1 0+(169568133/400000000 : ℝ)*X 1 1+(4493802897/10000000000 : ℝ)*X 1 2+(4364655839/10000000000 : ℝ)*X 2 0+(169568133/400000000 : ℝ)*X 2 1+(4493802897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2166860591/10000000000 : ℝ)*X 0 0+(2632866629/5000000000 : ℝ)*X 0 1+(1078611801/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312423397/10000000000 : ℝ)*X 1 0+(-1052060951/5000000000 : ℝ)*X 1 1+(2696529471/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312423451/10000000000 : ℝ)*X 2 0+(2696529421/5000000000 : ℝ)*X 2 1+(-420824393/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872933123/2000000000 : ℝ)*X 0 0+(4493159911/10000000000 : ℝ)*X 0 1+(529981093/1250000000 : ℝ)*X 0 2+(872933123/2000000000 : ℝ)*X 1 0+(4493159911/10000000000 : ℝ)*X 1 1+(529981093/1250000000 : ℝ)*X 1 2+(872933123/2000000000 : ℝ)*X 2 0+(4493159911/10000000000 : ℝ)*X 2 1+(529981093/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2046232900618569153060491529/346750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127676001/10000000000000 : ℝ)*(base19) + (1133623859/100000000000000 : ℝ)*(base23) + (29656413/50000000000000 : ℝ)*(lower2) + (33086387/20000000000000 : ℝ)*(upper3) + (68092227/100000000000000 : ℝ)*(upper5) + (5870987016121433/100000000000000 : ℝ)*(major0) + (5870987016121433/100000000000000 : ℝ)*(major1) + (5870987016121433/100000000000000 : ℝ)*(major2) + (7814167122108941/100000000000000 : ℝ)*(sp0) + (7814200180158093/100000000000000 : ℝ)*(sp1) + (1953550080823561/25000000000000 : ℝ)*(sp2) + (78555062718353/2000000000000 : ℝ)*(sp3) + (34334809161/100000000000000 : ℝ)*(sp4) + (769708049/4000000000000 : ℝ)*(sp7) + (981943094654719/25000000000000 : ℝ)*(f.failure) + (7814201456918103/100000000000000 : ℝ)*(f.sum) + (36692129934431/6935000000000000000000000000 : ℝ)*base65 + (3336180428200036157/1387000000000000000000000000000000 : ℝ)*base67 + (16519481437065036157/1387000000000000000000000000000000 : ℝ)*base69 + (26124053960179036157/1387000000000000000000000000000000 : ℝ)*base71 + (268301201753/866875000000000000000000000 : ℝ)*base74 + (5881262215504963843/1387000000000000000000000000000000 : ℝ)*base76 + (6692997489772036157/1387000000000000000000000000000000 : ℝ)*base77 + (10959053840780036157/1387000000000000000000000000000000 : ℝ)*base79 + (14372909081409/1733750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (907013/625000000000000000000 : ℝ)*base89 + (907013/625000000000000000000 : ℝ)*base91 + (907013/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12524950598817749881239/1387000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1786147097/100000000000000 : ℝ)*(base19) + (187052361/10000000000000 : ℝ)*(base23) + (31094173/20000000000000 : ℝ)*(upper3) + (15915349/100000000000000 : ℝ)*(lower4) + (6063183/3125000000000 : ℝ)*(upper5) + (590079324887143/10000000000000 : ℝ)*(major0) + (590079324887143/10000000000000 : ℝ)*(major1) + (590079324887143/10000000000000 : ℝ)*(major2) + (48407573191/100000000000000 : ℝ)*(sp1) + (1382604183/3125000000000 : ℝ)*(sp2) + (3926936515886811/50000000000000 : ℝ)*(sp4) + (1570764567610667/20000000000000 : ℝ)*(sp5) + (1963456729479039/25000000000000 : ℝ)*(sp6) + (789542632992209/20000000000000 : ℝ)*(sp7) + (789542632992209/20000000000000 : ℝ)*(f.failure) + (3926936515886811/50000000000000 : ℝ)*(f.sum) + (1915802003479/1387000000000000000000000000 : ℝ)*base66 + (183162990795043747/138700000000000000000000000000000 : ℝ)*base67 + (26434362910256253/138700000000000000000000000000000 : ℝ)*base70 + (167391665119443747/138700000000000000000000000000000 : ℝ)*base71 + (505942756063/173375000000000000000000000 : ℝ)*base74 + (3405183611364856253/138700000000000000000000000000000 : ℝ)*base76 + (1466018117307356253/138700000000000000000000000000000 : ℝ)*base78 + (1942025866882643747/138700000000000000000000000000000 : ℝ)*base79 + (143110985113/86687500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3585243/500000000000000000000 : ℝ)*base89 + (3585243/500000000000000000000 : ℝ)*base91 + (3585243/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1142_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1142_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1142_s7_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-541720549/2500000000 : ℝ)*x 0 + (2696531263/5000000000 : ℝ)*x 1 + (5265713531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541720549/2500000000 : ℝ)^8335 ≤ (6583436105901/50000000000000 : ℝ)^6287 := by
    have hnat : (541720549 : ℕ)^8335*50000000000000^6287 ≤ 6583436105901^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541720549 2500000000 6583436105901 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696531263/5000000000 : ℝ)^8335 ≤ (689128902979/1562500000000 : ℝ)^6287 := by
    have hnat : (2696531263 : ℕ)^8335*1562500000000^6287 ≤ 689128902979^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696531263 5000000000 689128902979 1562500000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265713531/10000000000 : ℝ)^8335 ≤ (42728877987257/100000000000000 : ℝ)^6287 := by
    have hnat : (5265713531 : ℕ)^8335*100000000000000^6287 ≤ 42728877987257^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265713531 10000000000 42728877987257 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541720549/2500000000 : ℝ), (2696531263/5000000000 : ℝ), (5265713531/10000000000 : ℝ)] ![(6583436105901/50000000000000 : ℝ), (689128902979/1562500000000 : ℝ), (42728877987257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541720549/2500000000 : ℝ)|^8335 ≤ (6583436105901/50000000000000 : ℝ)^6287
        have hw : |(-541720549/2500000000 : ℝ)|=(541720549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696531263/5000000000 : ℝ)|^8335 ≤ (689128902979/1562500000000 : ℝ)^6287
        have hw : |(2696531263/5000000000 : ℝ)|=(2696531263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265713531/10000000000 : ℝ)|^8335 ≤ (42728877987257/100000000000000 : ℝ)^6287
        have hw : |(5265713531/10000000000 : ℝ)|=(5265713531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s7_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344765691/10000000000 : ℝ)*x 0 + (-1115737927/5000000000 : ℝ)*x 1 + (5265713713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344765691/10000000000 : ℝ)^8335 ≤ (340479559119/781250000000 : ℝ)^6287 := by
    have hnat : (5344765691 : ℕ)^8335*781250000000^6287 ≤ 340479559119^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344765691 10000000000 340479559119 781250000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115737927/5000000000 : ℝ)^8335 ≤ (13689736475511/100000000000000 : ℝ)^6287 := by
    have hnat : (1115737927 : ℕ)^8335*100000000000000^6287 ≤ 13689736475511^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115737927 5000000000 13689736475511 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265713713/10000000000 : ℝ)^8335 ≤ (4272887994519/10000000000000 : ℝ)^6287 := by
    have hnat : (5265713713 : ℕ)^8335*10000000000000^6287 ≤ 4272887994519^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265713713 10000000000 4272887994519 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344765691/10000000000 : ℝ), (-1115737927/5000000000 : ℝ), (5265713713/10000000000 : ℝ)] ![(340479559119/781250000000 : ℝ), (13689736475511/100000000000000 : ℝ), (4272887994519/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344765691/10000000000 : ℝ)|^8335 ≤ (340479559119/781250000000 : ℝ)^6287
        have hw : |(5344765691/10000000000 : ℝ)|=(5344765691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115737927/5000000000 : ℝ)|^8335 ≤ (13689736475511/100000000000000 : ℝ)^6287
        have hw : |(-1115737927/5000000000 : ℝ)|=(1115737927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265713713/10000000000 : ℝ)|^8335 ≤ (4272887994519/10000000000000 : ℝ)^6287
        have hw : |(5265713713/10000000000 : ℝ)|=(5265713713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s7_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534476581/1000000000 : ℝ)*x 0 + (131642839/250000000 : ℝ)*x 1 + (-1115737949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534476581/1000000000 : ℝ)^8335 ≤ (2723836553353/6250000000000 : ℝ)^6287 := by
    have hnat : (534476581 : ℕ)^8335*6250000000000^6287 ≤ 2723836553353^6287*1000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534476581 1000000000 2723836553353 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131642839/250000000 : ℝ)^8335 ≤ (8545775659847/20000000000000 : ℝ)^6287 := by
    have hnat : (131642839 : ℕ)^8335*20000000000000^6287 ≤ 8545775659847^6287*250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131642839 250000000 8545775659847 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115737949/5000000000 : ℝ)^8335 ≤ (109517894667/800000000000 : ℝ)^6287 := by
    have hnat : (1115737949 : ℕ)^8335*800000000000^6287 ≤ 109517894667^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115737949 5000000000 109517894667 800000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534476581/1000000000 : ℝ), (131642839/250000000 : ℝ), (-1115737949/5000000000 : ℝ)] ![(2723836553353/6250000000000 : ℝ), (8545775659847/20000000000000 : ℝ), (109517894667/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534476581/1000000000 : ℝ)|^8335 ≤ (2723836553353/6250000000000 : ℝ)^6287
        have hw : |(534476581/1000000000 : ℝ)|=(534476581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131642839/250000000 : ℝ)|^8335 ≤ (8545775659847/20000000000000 : ℝ)^6287
        have hw : |(131642839/250000000 : ℝ)|=(131642839/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115737949/5000000000 : ℝ)|^8335 ≤ (109517894667/800000000000 : ℝ)^6287
        have hw : |(-1115737949/5000000000 : ℝ)|=(1115737949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s7_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436467193/1000000000 : ℝ)*x 0 + (2119911061/5000000000 : ℝ)*x 1 + (4493179779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436467193/1000000000 : ℝ)^8335 ≤ (16658476751371/50000000000000 : ℝ)^6287 := by
    have hnat : (436467193 : ℕ)^8335*50000000000000^6287 ≤ 16658476751371^6287*1000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436467193 1000000000 16658476751371 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119911061/5000000000 : ℝ)^8335 ≤ (3205941188913/10000000000000 : ℝ)^6287 := by
    have hnat : (2119911061 : ℕ)^8335*10000000000000^6287 ≤ 3205941188913^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119911061 5000000000 3205941188913 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493179779/10000000000 : ℝ)^8335 ≤ (17311817302599/50000000000000 : ℝ)^6287 := by
    have hnat : (4493179779 : ℕ)^8335*50000000000000^6287 ≤ 17311817302599^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493179779 10000000000 17311817302599 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436467193/1000000000 : ℝ), (2119911061/5000000000 : ℝ), (4493179779/10000000000 : ℝ)] ![(16658476751371/50000000000000 : ℝ), (3205941188913/10000000000000 : ℝ), (17311817302599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436467193/1000000000 : ℝ)|^8335 ≤ (16658476751371/50000000000000 : ℝ)^6287
        have hw : |(436467193/1000000000 : ℝ)|=(436467193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119911061/5000000000 : ℝ)|^8335 ≤ (3205941188913/10000000000000 : ℝ)^6287
        have hw : |(2119911061/5000000000 : ℝ)|=(2119911061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493179779/10000000000 : ℝ)|^8335 ≤ (17311817302599/50000000000000 : ℝ)^6287
        have hw : |(4493179779/10000000000 : ℝ)|=(4493179779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s7_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166886863/10000000000 : ℝ)*x 0 + (5266033721/10000000000 : ℝ)*x 1 + (1078548269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166886863/10000000000 : ℝ)^8335 ≤ (6583454904151/50000000000000 : ℝ)^6287 := by
    have hnat : (2166886863 : ℕ)^8335*50000000000000^6287 ≤ 6583454904151^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166886863 10000000000 6583454904151 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266033721/10000000000 : ℝ)^8335 ≤ (2670770161541/6250000000000 : ℝ)^6287 := by
    have hnat : (5266033721 : ℕ)^8335*6250000000000^6287 ≤ 2670770161541^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266033721 10000000000 2670770161541 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078548269/2000000000 : ℝ)^8335 ≤ (11025191899569/25000000000000 : ℝ)^6287 := by
    have hnat : (1078548269 : ℕ)^8335*25000000000000^6287 ≤ 11025191899569^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078548269 2000000000 11025191899569 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166886863/10000000000 : ℝ), (5266033721/10000000000 : ℝ), (1078548269/2000000000 : ℝ)] ![(6583454904151/50000000000000 : ℝ), (2670770161541/6250000000000 : ℝ), (11025191899569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166886863/10000000000 : ℝ)|^8335 ≤ (6583454904151/50000000000000 : ℝ)^6287
        have hw : |(-2166886863/10000000000 : ℝ)|=(2166886863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266033721/10000000000 : ℝ)|^8335 ≤ (2670770161541/6250000000000 : ℝ)^6287
        have hw : |(5266033721/10000000000 : ℝ)|=(5266033721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078548269/2000000000 : ℝ)|^8335 ≤ (11025191899569/25000000000000 : ℝ)^6287
        have hw : |(1078548269/2000000000 : ℝ)|=(1078548269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s7_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656250597/5000000000 : ℝ)*x 0 + (-2104448251/10000000000 : ℝ)*x 1 + (2696370671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656250597/5000000000 : ℝ)^8335 ≤ (21616470347543/50000000000000 : ℝ)^6287 := by
    have hnat : (2656250597 : ℕ)^8335*50000000000000^6287 ≤ 21616470347543^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656250597 5000000000 21616470347543 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104448251/10000000000 : ℝ)^8335 ≤ (12666291724583/100000000000000 : ℝ)^6287 := by
    have hnat : (2104448251 : ℕ)^8335*100000000000000^6287 ≤ 12666291724583^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104448251 10000000000 12666291724583 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696370671/5000000000 : ℝ)^8335 ≤ (44100767565751/100000000000000 : ℝ)^6287 := by
    have hnat : (2696370671 : ℕ)^8335*100000000000000^6287 ≤ 44100767565751^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696370671 5000000000 44100767565751 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656250597/5000000000 : ℝ), (-2104448251/10000000000 : ℝ), (2696370671/5000000000 : ℝ)] ![(21616470347543/50000000000000 : ℝ), (12666291724583/100000000000000 : ℝ), (44100767565751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656250597/5000000000 : ℝ)|^8335 ≤ (21616470347543/50000000000000 : ℝ)^6287
        have hw : |(2656250597/5000000000 : ℝ)|=(2656250597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104448251/10000000000 : ℝ)|^8335 ≤ (12666291724583/100000000000000 : ℝ)^6287
        have hw : |(-2104448251/10000000000 : ℝ)|=(2104448251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696370671/5000000000 : ℝ)|^8335 ≤ (44100767565751/100000000000000 : ℝ)^6287
        have hw : |(2696370671/5000000000 : ℝ)|=(2696370671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s7_6 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664062649/1250000000 : ℝ)*x 0 + (1078548269/2000000000 : ℝ)*x 1 + (-2104448249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664062649/1250000000 : ℝ)^8335 ≤ (10808235168377/25000000000000 : ℝ)^6287 := by
    have hnat : (664062649 : ℕ)^8335*25000000000000^6287 ≤ 10808235168377^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664062649 1250000000 10808235168377 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078548269/2000000000 : ℝ)^8335 ≤ (11025191899569/25000000000000 : ℝ)^6287 := by
    have hnat : (1078548269 : ℕ)^8335*25000000000000^6287 ≤ 11025191899569^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078548269 2000000000 11025191899569 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104448249/10000000000 : ℝ)^8335 ≤ (791643231789/6250000000000 : ℝ)^6287 := by
    have hnat : (2104448249 : ℕ)^8335*6250000000000^6287 ≤ 791643231789^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104448249 10000000000 791643231789 6250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664062649/1250000000 : ℝ), (1078548269/2000000000 : ℝ), (-2104448249/10000000000 : ℝ)] ![(10808235168377/25000000000000 : ℝ), (11025191899569/25000000000000 : ℝ), (791643231789/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664062649/1250000000 : ℝ)|^8335 ≤ (10808235168377/25000000000000 : ℝ)^6287
        have hw : |(664062649/1250000000 : ℝ)|=(664062649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078548269/2000000000 : ℝ)|^8335 ≤ (11025191899569/25000000000000 : ℝ)^6287
        have hw : |(1078548269/2000000000 : ℝ)|=(1078548269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2104448249/10000000000 : ℝ)|^8335 ≤ (791643231789/6250000000000 : ℝ)^6287
        have hw : |(-2104448249/10000000000 : ℝ)|=(2104448249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s7_7 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182340727/5000000000 : ℝ)*x 0 + (1123135743/2500000000 : ℝ)*x 1 + (4240461437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182340727/5000000000 : ℝ)^8335 ≤ (6663409976923/20000000000000 : ℝ)^6287 := by
    have hnat : (2182340727 : ℕ)^8335*20000000000000^6287 ≤ 6663409976923^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182340727 5000000000 6663409976923 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123135743/2500000000 : ℝ)^8335 ≤ (34617129133273/100000000000000 : ℝ)^6287 := by
    have hnat : (1123135743 : ℕ)^8335*100000000000000^6287 ≤ 34617129133273^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123135743 2500000000 34617129133273 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240461437/10000000000 : ℝ)^8335 ≤ (6413164193607/20000000000000 : ℝ)^6287 := by
    have hnat : (4240461437 : ℕ)^8335*20000000000000^6287 ≤ 6413164193607^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240461437 10000000000 6413164193607 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182340727/5000000000 : ℝ), (1123135743/2500000000 : ℝ), (4240461437/10000000000 : ℝ)] ![(6663409976923/20000000000000 : ℝ), (34617129133273/100000000000000 : ℝ), (6413164193607/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182340727/5000000000 : ℝ)|^8335 ≤ (6663409976923/20000000000000 : ℝ)^6287
        have hw : |(2182340727/5000000000 : ℝ)|=(2182340727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123135743/2500000000 : ℝ)|^8335 ≤ (34617129133273/100000000000000 : ℝ)^6287
        have hw : |(1123135743/2500000000 : ℝ)|=(1123135743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240461437/10000000000 : ℝ)|^8335 ≤ (6413164193607/20000000000000 : ℝ)^6287
        have hw : |(4240461437/10000000000 : ℝ)|=(4240461437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1419/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (281/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5673/50000 : ℝ) ^ (4167/1024 : ℝ) ≤ (3562687775472467/25000000000000000000 : ℝ) := by
    have hpowers : (5673/50000 : ℝ)^4167 ≤ (3562687775472467/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5673 : ℕ)^4167*25000000000000000000^1024 ≤ 3562687775472467^1024*50000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5673 50000 3562687775472467 25000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5673/50000 : ℝ)) (X := (3562687775472467/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14057/100000 : ℝ) ^ (4167/1024 : ℝ) ≤ (2129947674051523/6250000000000000000 : ℝ) := by
    have hpowers : (14057/100000 : ℝ)^4167 ≤ (2129947674051523/6250000000000000000 : ℝ)^1024 := by
      have hnat : (14057 : ℕ)^4167*6250000000000000000^1024 ≤ 2129947674051523^1024*100000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14057 100000 2129947674051523 6250000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14057/100000 : ℝ)) (X := (2129947674051523/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503562687775472467/12500000000000000000 : ℝ) ≤ (10000700321614927/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (12503562687775472467/12500000000000000000 : ℝ)^1024 ≤ (10000700321614927/10000000000000000 : ℝ)^4167 := by
      have hnat : (12503562687775472467 : ℕ)^1024*10000000000000000^4167 ≤ 10000700321614927^4167*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503562687775472467 12500000000000000000 10000700321614927 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000700321614927/10000000000000000 : ℝ)) (X := (12503562687775472467/12500000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012082478471678559/25000000000000000000 : ℝ) ≤ (1000118744454113/1000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (25012082478471678559/25000000000000000000 : ℝ)^1024 ≤ (1000118744454113/1000000000000000 : ℝ)^4167 := by
      have hnat : (25012082478471678559 : ℕ)^1024*1000000000000000^4167 ≤ 1000118744454113^4167*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012082478471678559 25000000000000000000 1000118744454113 1000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000118744454113/1000000000000000 : ℝ)) (X := (25012082478471678559/25000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127129947674051523/3125000000000000000 : ℝ) ≤ (10001674567467333/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (3127129947674051523/3125000000000000000 : ℝ)^1024 ≤ (10001674567467333/10000000000000000 : ℝ)^4167 := by
      have hnat : (3127129947674051523 : ℕ)^1024*10000000000000000^4167 ≤ 10001674567467333^4167*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127129947674051523 3125000000000000000 10001674567467333 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001674567467333/10000000000000000 : ℝ)) (X := (3127129947674051523/3125000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3562687775472467/25000000000000000000 : ℝ) ≤ ((27100844778456668621/27110000000000000000 : ℝ)+2*(487122926203/271100000000000 : ℝ)*(5673/50000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (27100844778456668621/27110000000000000000 : ℝ)+2*(487122926203/271100000000000 : ℝ)*(5673/50000 : ℝ)=(10000700321614927/10000000000000000 : ℝ) by norm_num, show 1+2*(3562687775472467/25000000000000000000 : ℝ)=(12503562687775472467/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2129947674051523/6250000000000000000 : ℝ)+(3562687775472467/25000000000000000000 : ℝ) ≤ ((27100844778456668621/27110000000000000000 : ℝ)+(487122926203/271100000000000 : ℝ)*((14057/100000 : ℝ)+(5673/50000 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (27100844778456668621/27110000000000000000 : ℝ)+(487122926203/271100000000000 : ℝ)*((14057/100000 : ℝ)+(5673/50000 : ℝ))=(1000118744454113/1000000000000000 : ℝ) by norm_num, show 1+(2129947674051523/6250000000000000000 : ℝ)+(3562687775472467/25000000000000000000 : ℝ)=(25012082478471678559/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2129947674051523/6250000000000000000 : ℝ) ≤ ((27100844778456668621/27110000000000000000 : ℝ)+2*(487122926203/271100000000000 : ℝ)*(14057/100000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (27100844778456668621/27110000000000000000 : ℝ)+2*(487122926203/271100000000000 : ℝ)*(14057/100000 : ℝ)=(10001674567467333/10000000000000000 : ℝ) by norm_num, show 1+2*(2129947674051523/6250000000000000000 : ℝ)=(3127129947674051523/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27100844778456668621/27110000000000000000 : ℝ)*(X 1 0+X 2 0)+(487122926203/271100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (27100844778456668621/27110000000000000000 : ℝ)) (alpha := (487122926203/271100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27100844778456668621/27110000000000000000 : ℝ)*(X 0 1+X 2 1)+(487122926203/271100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (27100844778456668621/27110000000000000000 : ℝ)) (alpha := (487122926203/271100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27100844778456668621/27110000000000000000 : ℝ)*(X 0 2+X 1 2)+(487122926203/271100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (5673/50000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (27100844778456668621/27110000000000000000 : ℝ)) (alpha := (487122926203/271100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-541720549/2500000000 : ℝ)*X 0 0+(2696531263/5000000000 : ℝ)*X 0 1+(5265713531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344765691/10000000000 : ℝ)*X 1 0+(-1115737927/5000000000 : ℝ)*X 1 1+(5265713713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534476581/1000000000 : ℝ)*X 2 0+(131642839/250000000 : ℝ)*X 2 1+(-1115737949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436467193/1000000000 : ℝ)*X 0 0+(2119911061/5000000000 : ℝ)*X 0 1+(4493179779/10000000000 : ℝ)*X 0 2+(436467193/1000000000 : ℝ)*X 1 0+(2119911061/5000000000 : ℝ)*X 1 1+(4493179779/10000000000 : ℝ)*X 1 2+(436467193/1000000000 : ℝ)*X 2 0+(2119911061/5000000000 : ℝ)*X 2 1+(4493179779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2166886863/10000000000 : ℝ)*X 0 0+(5266033721/10000000000 : ℝ)*X 0 1+(1078548269/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656250597/5000000000 : ℝ)*X 1 0+(-2104448251/10000000000 : ℝ)*X 1 1+(2696370671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664062649/1250000000 : ℝ)*X 2 0+(1078548269/2000000000 : ℝ)*X 2 1+(-2104448249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182340727/5000000000 : ℝ)*X 0 0+(1123135743/2500000000 : ℝ)*X 0 1+(4240461437/10000000000 : ℝ)*X 0 2+(2182340727/5000000000 : ℝ)*X 1 0+(1123135743/2500000000 : ℝ)*X 1 1+(4240461437/10000000000 : ℝ)*X 1 2+(2182340727/5000000000 : ℝ)*X 2 0+(1123135743/2500000000 : ℝ)*X 2 1+(4240461437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2878926661029112183192374033/338875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2413880841/100000000000000 : ℝ)*(base19) + (2533430673/100000000000000 : ℝ)*(base23) + (339615631/100000000000000 : ℝ)*(upper3) + (29549173/100000000000000 : ℝ)*(upper4) + (261346757/100000000000000 : ℝ)*(upper5) + (2949913525181409/50000000000000 : ℝ)*(major0) + (2949913525181409/50000000000000 : ℝ)*(major1) + (2949913525181409/50000000000000 : ℝ)*(major2) + (785251257299857/10000000000000 : ℝ)*(sp0) + (3926292319503417/50000000000000 : ℝ)*(sp1) + (3926292259728501/50000000000000 : ℝ)*(sp2) + (1973513309226809/50000000000000 : ℝ)*(sp3) + (4654993069/6250000000000 : ℝ)*(sp4) + (40146199613/100000000000000 : ℝ)*(sp7) + (246691672790827/6250000000000 : ℝ)*(f.failure) + (314103482115507/4000000000000 : ℝ)*(f.sum) + (1342796239103/423593750000000000000000000 : ℝ)*base66 + (7799131761527566989/1355500000000000000000000000000000 : ℝ)*base67 + (15146892215084066989/1355500000000000000000000000000000 : ℝ)*base69 + (9641248090622433011/1355500000000000000000000000000000 : ℝ)*base72 + (24643593259637/6777500000000000000000000000 : ℝ)*base73 + (11017959115878066989/1355500000000000000000000000000000 : ℝ)*base75 + (7469269987984566989/1355500000000000000000000000000000 : ℝ)*base77 + (16006300226689566989/1355500000000000000000000000000000 : ℝ)*base79 + (3744345067669/13555000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1894129/156250000000000000000 : ℝ)*base89 + (1894129/156250000000000000000 : ℝ)*base91 + (1894129/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4541640308453817570830799957/677750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1207801031/100000000000000 : ℝ)*(base19) + (263727861/20000000000000 : ℝ)*(base23) + (65744227/50000000000000 : ℝ)*(upper3) + (12971839/25000000000000 : ℝ)*(lower4) + (137237287/100000000000000 : ℝ)*(upper5) + (2964788479595139/50000000000000 : ℝ)*(major0) + (2964788479595139/50000000000000 : ℝ)*(major1) + (2964788479595139/50000000000000 : ℝ)*(major2) + (33269066719/100000000000000 : ℝ)*(sp1) + (35926319861/100000000000000 : ℝ)*(sp2) + (7892183825508107/100000000000000 : ℝ)*(sp4) + (1973037337160089/25000000000000 : ℝ)*(sp5) + (3946073290274471/50000000000000 : ℝ)*(sp6) + (158678794780157/4000000000000 : ℝ)*(sp7) + (158678794780157/4000000000000 : ℝ)*(f.failure) + (7892183825508107/100000000000000 : ℝ)*(f.sum) + (98180995359439/13555000000000000000000000000 : ℝ)*base65 + (13042717016821366681/1355500000000000000000000000000000 : ℝ)*base68 + (3957726178282866681/1355500000000000000000000000000000 : ℝ)*base70 + (28385173841300633319/1355500000000000000000000000000000 : ℝ)*base71 + (4908399262257/1694375000000000000000000000 : ℝ)*base74 + (1478599445155133319/1355500000000000000000000000000000 : ℝ)*base75 + (6530294499144866681/1355500000000000000000000000000000 : ℝ)*base78 + (31834753623887866681/1355500000000000000000000000000000 : ℝ)*base80 + (45285062941039/13555000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (96961/100000000000000000000 : ℝ)*base90 + (96961/100000000000000000000 : ℝ)*base92 + (96961/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1142_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1142_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1142_s8_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166889899/10000000000 : ℝ)*x 0 + (2696497939/5000000000 : ℝ)*x 1 + (5265774931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166889899/10000000000 : ℝ)^8335 ≤ (6583467132889/50000000000000 : ℝ)^6287 := by
    have hnat : (2166889899 : ℕ)^8335*50000000000000^6287 ≤ 6583467132889^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166889899 10000000000 6583467132889 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696497939/5000000000 : ℝ)^8335 ≤ (1102588179957/2500000000000 : ℝ)^6287 := by
    have hnat : (2696497939 : ℕ)^8335*2500000000000^6287 ≤ 1102588179957^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696497939 5000000000 1102588179957 2500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265774931/10000000000 : ℝ)^8335 ≤ (427295385219/1000000000000 : ℝ)^6287 := by
    have hnat : (5265774931 : ℕ)^8335*1000000000000^6287 ≤ 427295385219^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265774931 10000000000 427295385219 1000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166889899/10000000000 : ℝ), (2696497939/5000000000 : ℝ), (5265774931/10000000000 : ℝ)] ![(6583467132889/50000000000000 : ℝ), (1102588179957/2500000000000 : ℝ), (427295385219/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166889899/10000000000 : ℝ)|^8335 ≤ (6583467132889/50000000000000 : ℝ)^6287
        have hw : |(-2166889899/10000000000 : ℝ)|=(2166889899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696497939/5000000000 : ℝ)|^8335 ≤ (1102588179957/2500000000000 : ℝ)^6287
        have hw : |(2696497939/5000000000 : ℝ)|=(2696497939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265774931/10000000000 : ℝ)|^8335 ≤ (427295385219/1000000000000 : ℝ)^6287
        have hw : |(5265774931/10000000000 : ℝ)|=(5265774931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s8_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344748233/10000000000 : ℝ)*x 0 + (-278927267/1250000000 : ℝ)*x 1 + (5265774891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344748233/10000000000 : ℝ)^8335 ≤ (43581194842531/100000000000000 : ℝ)^6287 := by
    have hnat : (5344748233 : ℕ)^8335*100000000000000^6287 ≤ 43581194842531^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344748233 10000000000 43581194842531 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278927267/1250000000 : ℝ)^8335 ≤ (13689267041573/100000000000000 : ℝ)^6287 := by
    have hnat : (278927267 : ℕ)^8335*100000000000000^6287 ≤ 13689267041573^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278927267 1250000000 13689267041573 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265774891/10000000000 : ℝ)^8335 ≤ (667649032681/1562500000000 : ℝ)^6287 := by
    have hnat : (5265774891 : ℕ)^8335*1562500000000^6287 ≤ 667649032681^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265774891 10000000000 667649032681 1562500000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344748233/10000000000 : ℝ), (-278927267/1250000000 : ℝ), (5265774891/10000000000 : ℝ)] ![(43581194842531/100000000000000 : ℝ), (13689267041573/100000000000000 : ℝ), (667649032681/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344748233/10000000000 : ℝ)|^8335 ≤ (43581194842531/100000000000000 : ℝ)^6287
        have hw : |(5344748233/10000000000 : ℝ)|=(5344748233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-278927267/1250000000 : ℝ)|^8335 ≤ (13689267041573/100000000000000 : ℝ)^6287
        have hw : |(-278927267/1250000000 : ℝ)|=(278927267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265774891/10000000000 : ℝ)|^8335 ≤ (667649032681/1562500000000 : ℝ)^6287
        have hw : |(5265774891/10000000000 : ℝ)|=(5265774891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s8_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213789931/400000000 : ℝ)*x 0 + (5265774859/10000000000 : ℝ)*x 1 + (-557854531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213789931/400000000 : ℝ)^8335 ≤ (544764941207/1250000000000 : ℝ)^6287 := by
    have hnat : (213789931 : ℕ)^8335*1250000000000^6287 ≤ 544764941207^6287*400000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213789931 400000000 544764941207 1250000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265774859/10000000000 : ℝ)^8335 ≤ (4272953774733/10000000000000 : ℝ)^6287 := by
    have hnat : (5265774859 : ℕ)^8335*10000000000000^6287 ≤ 4272953774733^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265774859 10000000000 4272953774733 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (557854531/2500000000 : ℝ)^8335 ≤ (6844633471987/50000000000000 : ℝ)^6287 := by
    have hnat : (557854531 : ℕ)^8335*50000000000000^6287 ≤ 6844633471987^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557854531 2500000000 6844633471987 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213789931/400000000 : ℝ), (5265774859/10000000000 : ℝ), (-557854531/2500000000 : ℝ)] ![(544764941207/1250000000000 : ℝ), (4272953774733/10000000000000 : ℝ), (6844633471987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213789931/400000000 : ℝ)|^8335 ≤ (544764941207/1250000000000 : ℝ)^6287
        have hw : |(213789931/400000000 : ℝ)|=(213789931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265774859/10000000000 : ℝ)|^8335 ≤ (4272953774733/10000000000000 : ℝ)^6287
        have hw : |(5265774859/10000000000 : ℝ)|=(5265774859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-557854531/2500000000 : ℝ)|^8335 ≤ (6844633471987/50000000000000 : ℝ)^6287
        have hw : |(-557854531/2500000000 : ℝ)|=(557854531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s8_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364674997/10000000000 : ℝ)*x 0 + (529993639/1250000000 : ℝ)*x 1 + (4493052127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364674997/10000000000 : ℝ)^8335 ≤ (666339690809/2000000000000 : ℝ)^6287 := by
    have hnat : (4364674997 : ℕ)^8335*2000000000000^6287 ≤ 666339690809^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364674997 10000000000 666339690809 2000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529993639/1250000000 : ℝ)^8335 ≤ (16030342464053/50000000000000 : ℝ)^6287 := by
    have hnat : (529993639 : ℕ)^8335*50000000000000^6287 ≤ 16030342464053^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529993639 1250000000 16030342464053 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493052127/10000000000 : ℝ)^8335 ≤ (34622330518041/100000000000000 : ℝ)^6287 := by
    have hnat : (4493052127 : ℕ)^8335*100000000000000^6287 ≤ 34622330518041^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493052127 10000000000 34622330518041 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364674997/10000000000 : ℝ), (529993639/1250000000 : ℝ), (4493052127/10000000000 : ℝ)] ![(666339690809/2000000000000 : ℝ), (16030342464053/50000000000000 : ℝ), (34622330518041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364674997/10000000000 : ℝ)|^8335 ≤ (666339690809/2000000000000 : ℝ)^6287
        have hw : |(4364674997/10000000000 : ℝ)|=(4364674997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529993639/1250000000 : ℝ)|^8335 ≤ (16030342464053/50000000000000 : ℝ)^6287
        have hw : |(529993639/1250000000 : ℝ)|=(529993639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493052127/10000000000 : ℝ)|^8335 ≤ (34622330518041/100000000000000 : ℝ)^6287
        have hw : |(4493052127/10000000000 : ℝ)|=(4493052127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s8_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166894761/10000000000 : ℝ)*x 0 + (5266094337/10000000000 : ℝ)*x 1 + (10532569/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166894761/10000000000 : ℝ)^8335 ≤ (1645871679151/12500000000000 : ℝ)^6287 := by
    have hnat : (2166894761 : ℕ)^8335*12500000000000^6287 ≤ 1645871679151^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166894761 10000000000 1645871679151 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266094337/10000000000 : ℝ)^8335 ≤ (10683243674503/25000000000000 : ℝ)^6287 := by
    have hnat : (5266094337 : ℕ)^8335*25000000000000^6287 ≤ 10683243674503^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266094337 10000000000 10683243674503 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10532569/19531250 : ℝ)^8335 ≤ (1764002074441/4000000000000 : ℝ)^6287 := by
    have hnat : (10532569 : ℕ)^8335*4000000000000^6287 ≤ 1764002074441^6287*19531250^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10532569 19531250 1764002074441 4000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166894761/10000000000 : ℝ), (5266094337/10000000000 : ℝ), (10532569/19531250 : ℝ)] ![(1645871679151/12500000000000 : ℝ), (10683243674503/25000000000000 : ℝ), (1764002074441/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166894761/10000000000 : ℝ)|^8335 ≤ (1645871679151/12500000000000 : ℝ)^6287
        have hw : |(-2166894761/10000000000 : ℝ)|=(2166894761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266094337/10000000000 : ℝ)|^8335 ≤ (10683243674503/25000000000000 : ℝ)^6287
        have hw : |(5266094337/10000000000 : ℝ)|=(5266094337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10532569/19531250 : ℝ)|^8335 ≤ (1764002074441/4000000000000 : ℝ)^6287
        have hw : |(10532569/19531250 : ℝ)|=(10532569/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s8_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265625813/500000000 : ℝ)*x 0 + (-2104517647/10000000000 : ℝ)*x 1 + (2696337637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265625813/500000000 : ℝ)^8335 ≤ (8646620648199/20000000000000 : ℝ)^6287 := by
    have hnat : (265625813 : ℕ)^8335*20000000000000^6287 ≤ 8646620648199^6287*500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265625813 500000000 8646620648199 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104517647/10000000000 : ℝ)^8335 ≤ (12666845470007/100000000000000 : ℝ)^6287 := by
    have hnat : (2104517647 : ℕ)^8335*100000000000000^6287 ≤ 12666845470007^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104517647 10000000000 12666845470007 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696337637/5000000000 : ℝ)^8335 ≤ (22050025637787/50000000000000 : ℝ)^6287 := by
    have hnat : (2696337637 : ℕ)^8335*50000000000000^6287 ≤ 22050025637787^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696337637 5000000000 22050025637787 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265625813/500000000 : ℝ), (-2104517647/10000000000 : ℝ), (2696337637/5000000000 : ℝ)] ![(8646620648199/20000000000000 : ℝ), (12666845470007/100000000000000 : ℝ), (22050025637787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265625813/500000000 : ℝ)|^8335 ≤ (8646620648199/20000000000000 : ℝ)^6287
        have hw : |(265625813/500000000 : ℝ)|=(265625813/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104517647/10000000000 : ℝ)|^8335 ≤ (12666845470007/100000000000000 : ℝ)^6287
        have hw : |(-2104517647/10000000000 : ℝ)|=(2104517647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696337637/5000000000 : ℝ)|^8335 ≤ (22050025637787/50000000000000 : ℝ)^6287
        have hw : |(2696337637/5000000000 : ℝ)|=(2696337637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s8_6 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (26562581/50000000 : ℝ)*x 0 + (5392675329/10000000000 : ℝ)*x 1 + (-1052258827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26562581/50000000 : ℝ)^8335 ≤ (2161655129683/5000000000000 : ℝ)^6287 := by
    have hnat : (26562581 : ℕ)^8335*5000000000000^6287 ≤ 2161655129683^6287*50000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26562581 50000000 2161655129683 5000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392675329/10000000000 : ℝ)^8335 ≤ (44100051871867/100000000000000 : ℝ)^6287 := by
    have hnat : (5392675329 : ℕ)^8335*100000000000000^6287 ≤ 44100051871867^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392675329 10000000000 44100051871867 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052258827/5000000000 : ℝ)^8335 ≤ (12666845525863/100000000000000 : ℝ)^6287 := by
    have hnat : (1052258827 : ℕ)^8335*100000000000000^6287 ≤ 12666845525863^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052258827 5000000000 12666845525863 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26562581/50000000 : ℝ), (5392675329/10000000000 : ℝ), (-1052258827/5000000000 : ℝ)] ![(2161655129683/5000000000000 : ℝ), (44100051871867/100000000000000 : ℝ), (12666845525863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26562581/50000000 : ℝ)|^8335 ≤ (2161655129683/5000000000000 : ℝ)^6287
        have hw : |(26562581/50000000 : ℝ)|=(26562581/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392675329/10000000000 : ℝ)|^8335 ≤ (44100051871867/100000000000000 : ℝ)^6287
        have hw : |(5392675329/10000000000 : ℝ)|=(5392675329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052258827/5000000000 : ℝ)|^8335 ≤ (12666845525863/100000000000000 : ℝ)^6287
        have hw : |(-1052258827/5000000000 : ℝ)|=(1052258827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s8_7 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364684671/10000000000 : ℝ)*x 0 + (2246208271/5000000000 : ℝ)*x 1 + (212029351/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364684671/10000000000 : ℝ)^8335 ≤ (3331708244033/10000000000000 : ℝ)^6287 := by
    have hnat : (4364684671 : ℕ)^8335*10000000000000^6287 ≤ 3331708244033^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364684671 10000000000 3331708244033 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246208271/5000000000 : ℝ)^8335 ≤ (34615837589591/100000000000000 : ℝ)^6287 := by
    have hnat : (2246208271 : ℕ)^8335*100000000000000^6287 ≤ 34615837589591^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246208271 5000000000 34615837589591 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212029351/500000000 : ℝ)^8335 ≤ (16033539981999/50000000000000 : ℝ)^6287 := by
    have hnat : (212029351 : ℕ)^8335*50000000000000^6287 ≤ 16033539981999^6287*500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212029351 500000000 16033539981999 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364684671/10000000000 : ℝ), (2246208271/5000000000 : ℝ), (212029351/500000000 : ℝ)] ![(3331708244033/10000000000000 : ℝ), (34615837589591/100000000000000 : ℝ), (16033539981999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364684671/10000000000 : ℝ)|^8335 ≤ (3331708244033/10000000000000 : ℝ)^6287
        have hw : |(4364684671/10000000000 : ℝ)|=(4364684671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246208271/5000000000 : ℝ)|^8335 ≤ (34615837589591/100000000000000 : ℝ)^6287
        have hw : |(2246208271/5000000000 : ℝ)|=(2246208271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212029351/500000000 : ℝ)|^8335 ≤ (16033539981999/50000000000000 : ℝ)^6287
        have hw : |(212029351/500000000 : ℝ)|=(212029351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5677/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14049/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1419/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1419/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1419/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1419/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1419/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1419/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1419/12500 : ℝ) ^ (4167/1024 : ℝ) ≤ (14281442891558061/100000000000000000000 : ℝ) := by
    have hpowers : (1419/12500 : ℝ)^4167 ≤ (14281442891558061/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1419 : ℕ)^4167*100000000000000000000^1024 ≤ 14281442891558061^1024*12500^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1419 12500 14281442891558061 100000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1419/12500 : ℝ)) (X := (14281442891558061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (281/2000 : ℝ) ^ (4167/1024 : ℝ) ≤ (34010156929138409/100000000000000000000 : ℝ) := by
    have hpowers : (281/2000 : ℝ)^4167 ≤ (34010156929138409/100000000000000000000 : ℝ)^1024 := by
      have hnat : (281 : ℕ)^4167*100000000000000000000^1024 ≤ 34010156929138409^1024*2000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2000 34010156929138409 100000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2000 : ℝ)) (X := (34010156929138409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014281442891558061/50000000000000000000 : ℝ) ≤ (1250087728716569/1250000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50014281442891558061/50000000000000000000 : ℝ)^1024 ≤ (1250087728716569/1250000000000000 : ℝ)^4167 := by
      have hnat : (50014281442891558061 : ℕ)^1024*1250000000000000^4167 ≤ 1250087728716569^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014281442891558061 50000000000000000000 1250087728716569 1250000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250087728716569/1250000000000000 : ℝ)) (X := (50014281442891558061/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004829159982069647/10000000000000000000 : ℝ) ≤ (1250148312919113/1250000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (10004829159982069647/10000000000000000000 : ℝ)^1024 ≤ (1250148312919113/1250000000000000 : ℝ)^4167 := by
      have hnat : (10004829159982069647 : ℕ)^1024*1250000000000000^4167 ≤ 1250148312919113^4167*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004829159982069647 10000000000000000000 1250148312919113 1250000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250148312919113/1250000000000000 : ℝ)) (X := (10004829159982069647/10000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034010156929138409/50000000000000000000 : ℝ) ≤ (1250208897121657/1250000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50034010156929138409/50000000000000000000 : ℝ)^1024 ≤ (1250208897121657/1250000000000000 : ℝ)^4167 := by
      have hnat : (50034010156929138409 : ℕ)^1024*1250000000000000^4167 ≤ 1250208897121657^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034010156929138409 50000000000000000000 1250208897121657 1250000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250208897121657/1250000000000000 : ℝ)) (X := (50034010156929138409/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14281442891558061/100000000000000000000 : ℝ) ≤ ((1685680594171372093/1686250000000000000 : ℝ)+2*(3786512659/2107812500000 : ℝ)*(1419/12500 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (1685680594171372093/1686250000000000000 : ℝ)+2*(3786512659/2107812500000 : ℝ)*(1419/12500 : ℝ)=(1250087728716569/1250000000000000 : ℝ) by norm_num, show 1+2*(14281442891558061/100000000000000000000 : ℝ)=(50014281442891558061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34010156929138409/100000000000000000000 : ℝ)+(14281442891558061/100000000000000000000 : ℝ) ≤ ((1685680594171372093/1686250000000000000 : ℝ)+(3786512659/2107812500000 : ℝ)*((281/2000 : ℝ)+(1419/12500 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (1685680594171372093/1686250000000000000 : ℝ)+(3786512659/2107812500000 : ℝ)*((281/2000 : ℝ)+(1419/12500 : ℝ))=(1250148312919113/1250000000000000 : ℝ) by norm_num, show 1+(34010156929138409/100000000000000000000 : ℝ)+(14281442891558061/100000000000000000000 : ℝ)=(10004829159982069647/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34010156929138409/100000000000000000000 : ℝ) ≤ ((1685680594171372093/1686250000000000000 : ℝ)+2*(3786512659/2107812500000 : ℝ)*(281/2000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (1685680594171372093/1686250000000000000 : ℝ)+2*(3786512659/2107812500000 : ℝ)*(281/2000 : ℝ)=(1250208897121657/1250000000000000 : ℝ) by norm_num, show 1+2*(34010156929138409/100000000000000000000 : ℝ)=(50034010156929138409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1685680594171372093/1686250000000000000 : ℝ)*(X 1 0+X 2 0)+(3786512659/2107812500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (281/2000 : ℝ)) (c := (1685680594171372093/1686250000000000000 : ℝ)) (alpha := (3786512659/2107812500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1685680594171372093/1686250000000000000 : ℝ)*(X 0 1+X 2 1)+(3786512659/2107812500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (281/2000 : ℝ)) (c := (1685680594171372093/1686250000000000000 : ℝ)) (alpha := (3786512659/2107812500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1685680594171372093/1686250000000000000 : ℝ)*(X 0 2+X 1 2)+(3786512659/2107812500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (281/2000 : ℝ)) (c := (1685680594171372093/1686250000000000000 : ℝ)) (alpha := (3786512659/2107812500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2166889899/10000000000 : ℝ)*X 0 0+(2696497939/5000000000 : ℝ)*X 0 1+(5265774931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344748233/10000000000 : ℝ)*X 1 0+(-278927267/1250000000 : ℝ)*X 1 1+(5265774891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213789931/400000000 : ℝ)*X 2 0+(5265774859/10000000000 : ℝ)*X 2 1+(-557854531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364674997/10000000000 : ℝ)*X 0 0+(529993639/1250000000 : ℝ)*X 0 1+(4493052127/10000000000 : ℝ)*X 0 2+(4364674997/10000000000 : ℝ)*X 1 0+(529993639/1250000000 : ℝ)*X 1 1+(4493052127/10000000000 : ℝ)*X 1 2+(4364674997/10000000000 : ℝ)*X 2 0+(529993639/1250000000 : ℝ)*X 2 1+(4493052127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2166894761/10000000000 : ℝ)*X 0 0+(5266094337/10000000000 : ℝ)*X 0 1+(10532569/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265625813/500000000 : ℝ)*X 1 0+(-2104517647/10000000000 : ℝ)*X 1 1+(2696337637/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26562581/50000000 : ℝ)*X 2 0+(5392675329/10000000000 : ℝ)*X 2 1+(-1052258827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364684671/10000000000 : ℝ)*X 0 0+(2246208271/5000000000 : ℝ)*X 0 1+(212029351/500000000 : ℝ)*X 0 2+(4364684671/10000000000 : ℝ)*X 1 0+(2246208271/5000000000 : ℝ)*X 1 1+(212029351/500000000 : ℝ)*X 1 2+(4364684671/10000000000 : ℝ)*X 2 0+(2246208271/5000000000 : ℝ)*X 2 1+(212029351/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (355903518920847798218589303/84312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (179697511/25000000000000 : ℝ)*(base19) + (133082319/20000000000000 : ℝ)*(base23) + (61543/100000000000 : ℝ)*(lower2) + (5321581/5000000000000 : ℝ)*(upper3) + (13252493/25000000000000 : ℝ)*(upper5) + (5905676592974719/100000000000000 : ℝ)*(major0) + (5905676592974719/100000000000000 : ℝ)*(major1) + (5905676592974719/100000000000000 : ℝ)*(major2) + (7860356903858791/100000000000000 : ℝ)*(sp0) + (982546517003203/12500000000000 : ℝ)*(sp1) + (7860372189404073/100000000000000 : ℝ)*(sp2) + (197548464118391/5000000000000 : ℝ)*(sp3) + (15950956877/100000000000000 : ℝ)*(sp4) + (10908057857/100000000000000 : ℝ)*(sp7) + (987745047606419/25000000000000 : ℝ)*(f.failure) + (1965093213703917/25000000000000 : ℝ)*(f.sum) + (16738618690801/6745000000000000000000000000 : ℝ)*base66 + (1249332671673208133/168625000000000000000000000000000 : ℝ)*base68 + (50063742251208133/168625000000000000000000000000000 : ℝ)*base70 + (1646092727135958133/168625000000000000000000000000000 : ℝ)*base72 + (6683047167303/3372500000000000000000000000 : ℝ)*base74 + (48412550569083133/168625000000000000000000000000000 : ℝ)*base76 + (2139827010931833133/168625000000000000000000000000000 : ℝ)*base78 + (1576065810340708133/168625000000000000000000000000000 : ℝ)*base80 + (9124887663171/1686250000000000000000000000 : ℝ)*base81 + (617087/625000000000000000000 : ℝ)*base90 + (617087/625000000000000000000 : ℝ)*base92 + (617087/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3517710053481977936883/337250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1924342823/100000000000000 : ℝ)*(base19) + (1028058267/50000000000000 : ℝ)*(base23) + (668620151/100000000000000 : ℝ)*(lower1) + (175326927/100000000000000 : ℝ)*(upper3) + (21402803/20000000000000 : ℝ)*(lower4) + (213017183/100000000000000 : ℝ)*(upper5) + (1187093737857557/20000000000000 : ℝ)*(major0) + (1187093737857557/20000000000000 : ℝ)*(major1) + (1187093737857557/20000000000000 : ℝ)*(major2) + (1611923823/50000000000000 : ℝ)*(sp2) + (3950012755797953/50000000000000 : ℝ)*(sp4) + (1975005896813271/25000000000000 : ℝ)*(sp5) + (3950010115815863/50000000000000 : ℝ)*(sp6) + (1985455759646969/50000000000000 : ℝ)*(sp7) + (1985455759646969/50000000000000 : ℝ)*(f.failure) + (3950012755797953/50000000000000 : ℝ)*(f.sum) + (1141937491941/337250000000000000000000000 : ℝ)*base65 + (1861104811935193199/33725000000000000000000000000000 : ℝ)*base68 + (31084638142443199/33725000000000000000000000000000 : ℝ)*base70 + (1861573210852806801/33725000000000000000000000000000 : ℝ)*base71 + (72814080857/33725000000000000000000000 : ℝ)*base73 + (3992930289566243199/33725000000000000000000000000000 : ℝ)*base76 + (35528836165556801/33725000000000000000000000000000 : ℝ)*base77 + (184382692648456801/33725000000000000000000000000000 : ℝ)*base79 + (574183214421/337250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5652237/1250000000000000000000 : ℝ)*base90 + (5652237/1250000000000000000000 : ℝ)*base92 + (5652237/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1142_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1142_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1142_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1142_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1142_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1142_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1142_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

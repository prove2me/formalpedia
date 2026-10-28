-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1052_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:56:38.184648+00:00
-- url     : https://prove2.me/submissions/e5d50c35-adc0-4779-86de-bee53067a36f

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
theorem support_rectangle_w1052_box_0 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-416145487/2000000000 : ℝ)*x 0 + (67219487/125000000 : ℝ)*x 1 + (5377558851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416145487/2000000000 : ℝ)^8245 ≤ (1548129423971/12500000000000 : ℝ)^6197 := by
    have hnat : (416145487 : ℕ)^8245*12500000000000^6197 ≤ 1548129423971^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416145487 2000000000 1548129423971 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67219487/125000000 : ℝ)^8245 ≤ (10951870722247/25000000000000 : ℝ)^6197 := by
    have hnat : (67219487 : ℕ)^8245*25000000000000^6197 ≤ 10951870722247^6197*125000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67219487 125000000 10951870722247 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377558851/10000000000 : ℝ)^8245 ≤ (43807481707583/100000000000000 : ℝ)^6197 := by
    have hnat : (5377558851 : ℕ)^8245*100000000000000^6197 ≤ 43807481707583^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377558851 10000000000 43807481707583 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416145487/2000000000 : ℝ), (67219487/125000000 : ℝ), (5377558851/10000000000 : ℝ)] ![(1548129423971/12500000000000 : ℝ), (10951870722247/25000000000000 : ℝ), (43807481707583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416145487/2000000000 : ℝ)|^8245 ≤ (1548129423971/12500000000000 : ℝ)^6197
        have hw : |(-416145487/2000000000 : ℝ)|=(416145487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67219487/125000000 : ℝ)|^8245 ≤ (10951870722247/25000000000000 : ℝ)^6197
        have hw : |(67219487/125000000 : ℝ)|=(67219487/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377558851/10000000000 : ℝ)|^8245 ≤ (43807481707583/100000000000000 : ℝ)^6197
        have hw : |(5377558851/10000000000 : ℝ)|=(5377558851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_1 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295040709/10000000000 : ℝ)*x 0 + (-1096198459/5000000000 : ℝ)*x 1 + (1075511787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295040709/10000000000 : ℝ)^8245 ≤ (5364422257481/12500000000000 : ℝ)^6197 := by
    have hnat : (5295040709 : ℕ)^8245*12500000000000^6197 ≤ 5364422257481^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295040709 10000000000 5364422257481 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096198459/5000000000 : ℝ)^8245 ≤ (13277139316811/100000000000000 : ℝ)^6197 := by
    have hnat : (1096198459 : ℕ)^8245*100000000000000^6197 ≤ 13277139316811^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096198459 5000000000 13277139316811 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075511787/2000000000 : ℝ)^8245 ≤ (43807482618023/100000000000000 : ℝ)^6197 := by
    have hnat : (1075511787 : ℕ)^8245*100000000000000^6197 ≤ 43807482618023^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075511787 2000000000 43807482618023 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295040709/10000000000 : ℝ), (-1096198459/5000000000 : ℝ), (1075511787/2000000000 : ℝ)] ![(5364422257481/12500000000000 : ℝ), (13277139316811/100000000000000 : ℝ), (43807482618023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295040709/10000000000 : ℝ)|^8245 ≤ (5364422257481/12500000000000 : ℝ)^6197
        have hw : |(5295040709/10000000000 : ℝ)|=(5295040709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096198459/5000000000 : ℝ)|^8245 ≤ (13277139316811/100000000000000 : ℝ)^6197
        have hw : |(-1096198459/5000000000 : ℝ)|=(1096198459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075511787/2000000000 : ℝ)|^8245 ≤ (43807482618023/100000000000000 : ℝ)^6197
        have hw : |(1075511787/2000000000 : ℝ)|=(1075511787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_2 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (529504069/1000000000 : ℝ)*x 0 + (1344389721/2500000000 : ℝ)*x 1 + (-219239701/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529504069/1000000000 : ℝ)^8245 ≤ (8583075570993/20000000000000 : ℝ)^6197 := by
    have hnat : (529504069 : ℕ)^8245*20000000000000^6197 ≤ 8583075570993^6197*1000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529504069 1000000000 8583075570993 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344389721/2500000000 : ℝ)^8245 ≤ (5475935258157/12500000000000 : ℝ)^6197 := by
    have hnat : (1344389721 : ℕ)^8245*12500000000000^6197 ≤ 5475935258157^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344389721 2500000000 5475935258157 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219239701/1000000000 : ℝ)^8245 ≤ (13277140058091/100000000000000 : ℝ)^6197 := by
    have hnat : (219239701 : ℕ)^8245*100000000000000^6197 ≤ 13277140058091^6197*1000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219239701 1000000000 13277140058091 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529504069/1000000000 : ℝ), (1344389721/2500000000 : ℝ), (-219239701/1000000000 : ℝ)] ![(8583075570993/20000000000000 : ℝ), (5475935258157/12500000000000 : ℝ), (13277140058091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529504069/1000000000 : ℝ)|^8245 ≤ (8583075570993/20000000000000 : ℝ)^6197
        have hw : |(529504069/1000000000 : ℝ)|=(529504069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344389721/2500000000 : ℝ)|^8245 ≤ (5475935258157/12500000000000 : ℝ)^6197
        have hw : |(1344389721/2500000000 : ℝ)|=(1344389721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219239701/1000000000 : ℝ)|^8245 ≤ (13277140058091/100000000000000 : ℝ)^6197
        have hw : |(-219239701/1000000000 : ℝ)|=(219239701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_3 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4486065197/10000000000 : ℝ)*x 0 + (4325406281/10000000000 : ℝ)*x 1 + (2162703089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4486065197/10000000000 : ℝ)^8245 ≤ (17210094504727/50000000000000 : ℝ)^6197 := by
    have hnat : (4486065197 : ℕ)^8245*50000000000000^6197 ≤ 17210094504727^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486065197 10000000000 17210094504727 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4325406281/10000000000 : ℝ)^8245 ≤ (16394953004523/50000000000000 : ℝ)^6197 := by
    have hnat : (4325406281 : ℕ)^8245*50000000000000^6197 ≤ 16394953004523^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325406281 10000000000 16394953004523 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2162703089/5000000000 : ℝ)^8245 ≤ (32789904970179/100000000000000 : ℝ)^6197 := by
    have hnat : (2162703089 : ℕ)^8245*100000000000000^6197 ≤ 32789904970179^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162703089 5000000000 32789904970179 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4486065197/10000000000 : ℝ), (4325406281/10000000000 : ℝ), (2162703089/5000000000 : ℝ)] ![(17210094504727/50000000000000 : ℝ), (16394953004523/50000000000000 : ℝ), (32789904970179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4486065197/10000000000 : ℝ)|^8245 ≤ (17210094504727/50000000000000 : ℝ)^6197
        have hw : |(4486065197/10000000000 : ℝ)|=(4486065197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4325406281/10000000000 : ℝ)|^8245 ≤ (16394953004523/50000000000000 : ℝ)^6197
        have hw : |(4325406281/10000000000 : ℝ)|=(4325406281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2162703089/5000000000 : ℝ)|^8245 ≤ (32789904970179/100000000000000 : ℝ)^6197
        have hw : |(2162703089/5000000000 : ℝ)|=(2162703089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_4 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2342025273/10000000000 : ℝ)*x 0 + (1319968931/2500000000 : ℝ)*x 1 + (5279875579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2342025273/10000000000 : ℝ)^8245 ≤ (7248074278973/50000000000000 : ℝ)^6197 := by
    have hnat : (2342025273 : ℕ)^8245*50000000000000^6197 ≤ 7248074278973^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2342025273 10000000000 7248074278973 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319968931/2500000000 : ℝ)^8245 ≤ (21375963248407/50000000000000 : ℝ)^6197 := by
    have hnat : (1319968931 : ℕ)^8245*50000000000000^6197 ≤ 21375963248407^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319968931 2500000000 21375963248407 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279875579/10000000000 : ℝ)^8245 ≤ (42751924934713/100000000000000 : ℝ)^6197 := by
    have hnat : (5279875579 : ℕ)^8245*100000000000000^6197 ≤ 42751924934713^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279875579 10000000000 42751924934713 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2342025273/10000000000 : ℝ), (1319968931/2500000000 : ℝ), (5279875579/10000000000 : ℝ)] ![(7248074278973/50000000000000 : ℝ), (21375963248407/50000000000000 : ℝ), (42751924934713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2342025273/10000000000 : ℝ)|^8245 ≤ (7248074278973/50000000000000 : ℝ)^6197
        have hw : |(-2342025273/10000000000 : ℝ)|=(2342025273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319968931/2500000000 : ℝ)|^8245 ≤ (21375963248407/50000000000000 : ℝ)^6197
        have hw : |(1319968931/2500000000 : ℝ)|=(1319968931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279875579/10000000000 : ℝ)|^8245 ≤ (42751924934713/100000000000000 : ℝ)^6197
        have hw : |(5279875579/10000000000 : ℝ)|=(5279875579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_5 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33526219/62500000 : ℝ)*x 0 + (-2230542819/10000000000 : ℝ)*x 1 + (5279875809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33526219/62500000 : ℝ)^8245 ≤ (10915674130279/25000000000000 : ℝ)^6197 := by
    have hnat : (33526219 : ℕ)^8245*25000000000000^6197 ≤ 10915674130279^6197*62500000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33526219 62500000 10915674130279 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2230542819/10000000000 : ℝ)^8245 ≤ (13585376056743/100000000000000 : ℝ)^6197 := by
    have hnat : (2230542819 : ℕ)^8245*100000000000000^6197 ≤ 13585376056743^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230542819 10000000000 13585376056743 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279875809/10000000000 : ℝ)^8245 ≤ (2671995463283/6250000000000 : ℝ)^6197 := by
    have hnat : (5279875809 : ℕ)^8245*6250000000000^6197 ≤ 2671995463283^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279875809 10000000000 2671995463283 6250000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33526219/62500000 : ℝ), (-2230542819/10000000000 : ℝ), (5279875809/10000000000 : ℝ)] ![(10915674130279/25000000000000 : ℝ), (13585376056743/100000000000000 : ℝ), (2671995463283/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33526219/62500000 : ℝ)|^8245 ≤ (10915674130279/25000000000000 : ℝ)^6197
        have hw : |(33526219/62500000 : ℝ)|=(33526219/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2230542819/10000000000 : ℝ)|^8245 ≤ (13585376056743/100000000000000 : ℝ)^6197
        have hw : |(-2230542819/10000000000 : ℝ)|=(2230542819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279875809/10000000000 : ℝ)|^8245 ≤ (2671995463283/6250000000000 : ℝ)^6197
        have hw : |(5279875809/10000000000 : ℝ)|=(5279875809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_6 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1341048937/2500000000 : ℝ)*x 0 + (2639937641/5000000000 : ℝ)*x 1 + (-2230542573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341048937/2500000000 : ℝ)^8245 ≤ (43662704188521/100000000000000 : ℝ)^6197 := by
    have hnat : (1341048937 : ℕ)^8245*100000000000000^6197 ≤ 43662704188521^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341048937 2500000000 43662704188521 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639937641/5000000000 : ℝ)^8245 ≤ (42751921735099/100000000000000 : ℝ)^6197 := by
    have hnat : (2639937641 : ℕ)^8245*100000000000000^6197 ≤ 42751921735099^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639937641 5000000000 42751921735099 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230542573/10000000000 : ℝ)^8245 ≤ (13585374063293/100000000000000 : ℝ)^6197 := by
    have hnat : (2230542573 : ℕ)^8245*100000000000000^6197 ≤ 13585374063293^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230542573 10000000000 13585374063293 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341048937/2500000000 : ℝ), (2639937641/5000000000 : ℝ), (-2230542573/10000000000 : ℝ)] ![(43662704188521/100000000000000 : ℝ), (42751921735099/100000000000000 : ℝ), (13585374063293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341048937/2500000000 : ℝ)|^8245 ≤ (43662704188521/100000000000000 : ℝ)^6197
        have hw : |(1341048937/2500000000 : ℝ)|=(1341048937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639937641/5000000000 : ℝ)|^8245 ≤ (42751921735099/100000000000000 : ℝ)^6197
        have hw : |(2639937641/5000000000 : ℝ)|=(2639937641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230542573/10000000000 : ℝ)|^8245 ≤ (13585374063293/100000000000000 : ℝ)^6197
        have hw : |(-2230542573/10000000000 : ℝ)|=(2230542573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_7 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2134316907/5000000000 : ℝ)*x 0 + (4434100139/10000000000 : ℝ)*x 1 + (2217050273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134316907/5000000000 : ℝ)^8245 ≤ (16109269952091/50000000000000 : ℝ)^6197 := by
    have hnat : (2134316907 : ℕ)^8245*50000000000000^6197 ≤ 16109269952091^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134316907 5000000000 16109269952091 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4434100139/10000000000 : ℝ)^8245 ≤ (16945363985341/50000000000000 : ℝ)^6197 := by
    have hnat : (4434100139 : ℕ)^8245*50000000000000^6197 ≤ 16945363985341^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434100139 10000000000 16945363985341 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217050273/5000000000 : ℝ)^8245 ≤ (1355629284381/4000000000000 : ℝ)^6197 := by
    have hnat : (2217050273 : ℕ)^8245*4000000000000^6197 ≤ 1355629284381^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217050273 5000000000 1355629284381 4000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134316907/5000000000 : ℝ), (4434100139/10000000000 : ℝ), (2217050273/5000000000 : ℝ)] ![(16109269952091/50000000000000 : ℝ), (16945363985341/50000000000000 : ℝ), (1355629284381/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134316907/5000000000 : ℝ)|^8245 ≤ (16109269952091/50000000000000 : ℝ)^6197
        have hw : |(2134316907/5000000000 : ℝ)|=(2134316907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4434100139/10000000000 : ℝ)|^8245 ≤ (16945363985341/50000000000000 : ℝ)^6197
        have hw : |(4434100139/10000000000 : ℝ)|=(4434100139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2217050273/5000000000 : ℝ)|^8245 ≤ (1355629284381/4000000000000 : ℝ)^6197
        have hw : |(2217050273/5000000000 : ℝ)|=(2217050273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_8 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-142968413/625000000 : ℝ)*x 0 + (1042723903/2000000000 : ℝ)*x 1 + (5387158253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (142968413/625000000 : ℝ)^8245 ≤ (14048818499961/100000000000000 : ℝ)^6197 := by
    have hnat : (142968413 : ℕ)^8245*100000000000000^6197 ≤ 14048818499961^6197*625000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142968413 625000000 14048818499961 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042723903/2000000000 : ℝ)^8245 ≤ (1050990630809/2500000000000 : ℝ)^6197 := by
    have hnat : (1042723903 : ℕ)^8245*2500000000000^6197 ≤ 1050990630809^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042723903 2000000000 1050990630809 2500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387158253/10000000000 : ℝ)^8245 ≤ (21955778122989/50000000000000 : ℝ)^6197 := by
    have hnat : (5387158253 : ℕ)^8245*50000000000000^6197 ≤ 21955778122989^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387158253 10000000000 21955778122989 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-142968413/625000000 : ℝ), (1042723903/2000000000 : ℝ), (5387158253/10000000000 : ℝ)] ![(14048818499961/100000000000000 : ℝ), (1050990630809/2500000000000 : ℝ), (21955778122989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-142968413/625000000 : ℝ)|^8245 ≤ (14048818499961/100000000000000 : ℝ)^6197
        have hw : |(-142968413/625000000 : ℝ)|=(142968413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042723903/2000000000 : ℝ)|^8245 ≤ (1050990630809/2500000000000 : ℝ)^6197
        have hw : |(1042723903/2000000000 : ℝ)|=(1042723903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387158253/10000000000 : ℝ)|^8245 ≤ (21955778122989/50000000000000 : ℝ)^6197
        have hw : |(5387158253/10000000000 : ℝ)|=(5387158253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_9 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322060259/2500000000 : ℝ)*x 0 + (-2188577537/10000000000 : ℝ)*x 1 + (1346789547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322060259/2500000000 : ℝ)^8245 ≤ (42842070520997/100000000000000 : ℝ)^6197 := by
    have hnat : (1322060259 : ℕ)^8245*100000000000000^6197 ≤ 42842070520997^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322060259 2500000000 42842070520997 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188577537/10000000000 : ℝ)^8245 ≤ (1655796741153/12500000000000 : ℝ)^6197 := by
    have hnat : (2188577537 : ℕ)^8245*12500000000000^6197 ≤ 1655796741153^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188577537 10000000000 1655796741153 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346789547/2500000000 : ℝ)^8245 ≤ (8782311108211/20000000000000 : ℝ)^6197 := by
    have hnat : (1346789547 : ℕ)^8245*20000000000000^6197 ≤ 8782311108211^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346789547 2500000000 8782311108211 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322060259/2500000000 : ℝ), (-2188577537/10000000000 : ℝ), (1346789547/2500000000 : ℝ)] ![(42842070520997/100000000000000 : ℝ), (1655796741153/12500000000000 : ℝ), (8782311108211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322060259/2500000000 : ℝ)|^8245 ≤ (42842070520997/100000000000000 : ℝ)^6197
        have hw : |(1322060259/2500000000 : ℝ)|=(1322060259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2188577537/10000000000 : ℝ)|^8245 ≤ (1655796741153/12500000000000 : ℝ)^6197
        have hw : |(-2188577537/10000000000 : ℝ)|=(2188577537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346789547/2500000000 : ℝ)|^8245 ≤ (8782311108211/20000000000000 : ℝ)^6197
        have hw : |(1346789547/2500000000 : ℝ)|=(1346789547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_10 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322060277/2500000000 : ℝ)*x 0 + (5387158207/10000000000 : ℝ)*x 1 + (-1094288707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322060277/2500000000 : ℝ)^8245 ≤ (42842071297067/100000000000000 : ℝ)^6197 := by
    have hnat : (1322060277 : ℕ)^8245*100000000000000^6197 ≤ 42842071297067^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322060277 2500000000 42842071297067 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387158207/10000000000 : ℝ)^8245 ≤ (43911555747109/100000000000000 : ℝ)^6197 := by
    have hnat : (5387158207 : ℕ)^8245*100000000000000^6197 ≤ 43911555747109^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387158207 10000000000 43911555747109 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094288707/5000000000 : ℝ)^8245 ≤ (827898308671/6250000000000 : ℝ)^6197 := by
    have hnat : (1094288707 : ℕ)^8245*6250000000000^6197 ≤ 827898308671^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094288707 5000000000 827898308671 6250000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322060277/2500000000 : ℝ), (5387158207/10000000000 : ℝ), (-1094288707/5000000000 : ℝ)] ![(42842071297067/100000000000000 : ℝ), (43911555747109/100000000000000 : ℝ), (827898308671/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322060277/2500000000 : ℝ)|^8245 ≤ (42842071297067/100000000000000 : ℝ)^6197
        have hw : |(1322060277/2500000000 : ℝ)|=(1322060277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387158207/10000000000 : ℝ)|^8245 ≤ (43911555747109/100000000000000 : ℝ)^6197
        have hw : |(5387158207/10000000000 : ℝ)|=(5387158207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1094288707/5000000000 : ℝ)|^8245 ≤ (827898308671/6250000000000 : ℝ)^6197
        have hw : |(-1094288707/5000000000 : ℝ)|=(1094288707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_11 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (180286351/400000000 : ℝ)*x 0 + (4314718849/10000000000 : ℝ)*x 1 + (2157359479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180286351/400000000 : ℝ)^8245 ≤ (34635687402323/100000000000000 : ℝ)^6197 := by
    have hnat : (180286351 : ℕ)^8245*100000000000000^6197 ≤ 34635687402323^6197*400000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180286351 400000000 34635687402323 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4314718849/10000000000 : ℝ)^8245 ≤ (32682155745047/100000000000000 : ℝ)^6197 := by
    have hnat : (4314718849 : ℕ)^8245*100000000000000^6197 ≤ 32682155745047^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314718849 10000000000 32682155745047 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157359479/5000000000 : ℝ)^8245 ≤ (32682156843531/100000000000000 : ℝ)^6197 := by
    have hnat : (2157359479 : ℕ)^8245*100000000000000^6197 ≤ 32682156843531^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157359479 5000000000 32682156843531 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(180286351/400000000 : ℝ), (4314718849/10000000000 : ℝ), (2157359479/5000000000 : ℝ)] ![(34635687402323/100000000000000 : ℝ), (32682155745047/100000000000000 : ℝ), (32682156843531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(180286351/400000000 : ℝ)|^8245 ≤ (34635687402323/100000000000000 : ℝ)^6197
        have hw : |(180286351/400000000 : ℝ)|=(180286351/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4314718849/10000000000 : ℝ)|^8245 ≤ (32682155745047/100000000000000 : ℝ)^6197
        have hw : |(4314718849/10000000000 : ℝ)|=(4314718849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2157359479/5000000000 : ℝ)|^8245 ≤ (32682156843531/100000000000000 : ℝ)^6197
        have hw : |(2157359479/5000000000 : ℝ)|=(2157359479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_12 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135635907/10000000000 : ℝ)*x 0 + (1360617161/2500000000 : ℝ)*x 1 + (5271881689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135635907/10000000000 : ℝ)^8245 ≤ (2564352318629/20000000000000 : ℝ)^6197 := by
    have hnat : (2135635907 : ℕ)^8245*20000000000000^6197 ≤ 2564352318629^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135635907 10000000000 2564352318629 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360617161/2500000000 : ℝ)^8245 ≤ (22256205488849/50000000000000 : ℝ)^6197 := by
    have hnat : (1360617161 : ℕ)^8245*50000000000000^6197 ≤ 22256205488849^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360617161 2500000000 22256205488849 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271881689/10000000000 : ℝ)^8245 ≤ (1706633096803/4000000000000 : ℝ)^6197 := by
    have hnat : (5271881689 : ℕ)^8245*4000000000000^6197 ≤ 1706633096803^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271881689 10000000000 1706633096803 4000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135635907/10000000000 : ℝ), (1360617161/2500000000 : ℝ), (5271881689/10000000000 : ℝ)] ![(2564352318629/20000000000000 : ℝ), (22256205488849/50000000000000 : ℝ), (1706633096803/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135635907/10000000000 : ℝ)|^8245 ≤ (2564352318629/20000000000000 : ℝ)^6197
        have hw : |(-2135635907/10000000000 : ℝ)|=(2135635907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360617161/2500000000 : ℝ)|^8245 ≤ (22256205488849/50000000000000 : ℝ)^6197
        have hw : |(1360617161/2500000000 : ℝ)|=(1360617161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271881689/10000000000 : ℝ)|^8245 ≤ (1706633096803/4000000000000 : ℝ)^6197
        have hw : |(5271881689/10000000000 : ℝ)|=(5271881689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_13 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369851719/10000000000 : ℝ)*x 0 + (-2233605517/10000000000 : ℝ)*x 1 + (263594109/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369851719/10000000000 : ℝ)^8245 ≤ (43723967150757/100000000000000 : ℝ)^6197 := by
    have hnat : (5369851719 : ℕ)^8245*100000000000000^6197 ≤ 43723967150757^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369851719 10000000000 43723967150757 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2233605517/10000000000 : ℝ)^8245 ≤ (3402550030921/25000000000000 : ℝ)^6197 := by
    have hnat : (2233605517 : ℕ)^8245*25000000000000^6197 ≤ 3402550030921^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233605517 10000000000 3402550030921 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263594109/500000000 : ℝ)^8245 ≤ (1706633308281/4000000000000 : ℝ)^6197 := by
    have hnat : (263594109 : ℕ)^8245*4000000000000^6197 ≤ 1706633308281^6197*500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263594109 500000000 1706633308281 4000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369851719/10000000000 : ℝ), (-2233605517/10000000000 : ℝ), (263594109/500000000 : ℝ)] ![(43723967150757/100000000000000 : ℝ), (3402550030921/25000000000000 : ℝ), (1706633308281/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369851719/10000000000 : ℝ)|^8245 ≤ (43723967150757/100000000000000 : ℝ)^6197
        have hw : |(5369851719/10000000000 : ℝ)|=(5369851719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2233605517/10000000000 : ℝ)|^8245 ≤ (3402550030921/25000000000000 : ℝ)^6197
        have hw : |(-2233605517/10000000000 : ℝ)|=(2233605517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263594109/500000000 : ℝ)|^8245 ≤ (1706633308281/4000000000000 : ℝ)^6197
        have hw : |(263594109/500000000 : ℝ)|=(263594109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_14 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684925767/5000000000 : ℝ)*x 0 + (5271882191/10000000000 : ℝ)*x 1 + (-2233605749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684925767/5000000000 : ℝ)^8245 ≤ (4372396514657/10000000000000 : ℝ)^6197 := by
    have hnat : (2684925767 : ℕ)^8245*10000000000000^6197 ≤ 4372396514657^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684925767 5000000000 4372396514657 10000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271882191/10000000000 : ℝ)^8245 ≤ (4266583282547/10000000000000 : ℝ)^6197 := by
    have hnat : (5271882191 : ℕ)^8245*10000000000000^6197 ≤ 4266583282547^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271882191 10000000000 4266583282547 10000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2233605749/10000000000 : ℝ)^8245 ≤ (13610202004539/100000000000000 : ℝ)^6197 := by
    have hnat : (2233605749 : ℕ)^8245*100000000000000^6197 ≤ 13610202004539^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233605749 10000000000 13610202004539 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684925767/5000000000 : ℝ), (5271882191/10000000000 : ℝ), (-2233605749/10000000000 : ℝ)] ![(4372396514657/10000000000000 : ℝ), (4266583282547/10000000000000 : ℝ), (13610202004539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684925767/5000000000 : ℝ)|^8245 ≤ (4372396514657/10000000000000 : ℝ)^6197
        have hw : |(2684925767/5000000000 : ℝ)|=(2684925767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271882191/10000000000 : ℝ)|^8245 ≤ (4266583282547/10000000000000 : ℝ)^6197
        have hw : |(5271882191/10000000000 : ℝ)|=(5271882191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2233605749/10000000000 : ℝ)|^8245 ≤ (13610202004539/100000000000000 : ℝ)^6197
        have hw : |(-2233605749/10000000000 : ℝ)|=(2233605749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_box_15 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4250609829/10000000000 : ℝ)*x 0 + (177719637/400000000 : ℝ)*x 1 + (4442990309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250609829/10000000000 : ℝ)^8245 ≤ (32037666993139/100000000000000 : ℝ)^6197 := by
    have hnat : (4250609829 : ℕ)^8245*100000000000000^6197 ≤ 32037666993139^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250609829 10000000000 32037666993139 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177719637/400000000 : ℝ)^8245 ≤ (8495292407701/25000000000000 : ℝ)^6197 := by
    have hnat : (177719637 : ℕ)^8245*25000000000000^6197 ≤ 8495292407701^6197*400000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177719637 400000000 8495292407701 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4442990309/10000000000 : ℝ)^8245 ≤ (33981163362461/100000000000000 : ℝ)^6197 := by
    have hnat : (4442990309 : ℕ)^8245*100000000000000^6197 ≤ 33981163362461^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442990309 10000000000 33981163362461 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250609829/10000000000 : ℝ), (177719637/400000000 : ℝ), (4442990309/10000000000 : ℝ)] ![(32037666993139/100000000000000 : ℝ), (8495292407701/25000000000000 : ℝ), (33981163362461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250609829/10000000000 : ℝ)|^8245 ≤ (32037666993139/100000000000000 : ℝ)^6197
        have hw : |(4250609829/10000000000 : ℝ)|=(4250609829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(177719637/400000000 : ℝ)|^8245 ≤ (8495292407701/25000000000000 : ℝ)^6197
        have hw : |(177719637/400000000 : ℝ)|=(177719637/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4442990309/10000000000 : ℝ)|^8245 ≤ (33981163362461/100000000000000 : ℝ)^6197
        have hw : |(4442990309/10000000000 : ℝ)|=(4442990309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1052_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5923/10000 : ℝ) ∧ (9941/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82921/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (351/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (351/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (351/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (351/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (351/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (351/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (351/3125 : ℝ) ^ (2061/512 : ℝ) ≤ (15056321901276127/100000000000000000000 : ℝ) := by
    have hpowers : (351/3125 : ℝ)^2061 ≤ (15056321901276127/100000000000000000000 : ℝ)^512 := by
      have hnat : (351 : ℕ)^2061*100000000000000000000^512 ≤ 15056321901276127^512*3125^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 3125 15056321901276127 100000000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/3125 : ℝ)) (X := (15056321901276127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hpowhi : (6997/50000 : ℝ) ^ (2061/512 : ℝ) ≤ (36482316656934251/100000000000000000000 : ℝ) := by
    have hpowers : (6997/50000 : ℝ)^2061 ≤ (36482316656934251/100000000000000000000 : ℝ)^512 := by
      have hnat : (6997 : ℕ)^2061*100000000000000000000^512 ≤ 36482316656934251^512*50000^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6997 50000 36482316656934251 100000000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6997/50000 : ℝ)) (X := (36482316656934251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015056321901276127/50000000000000000000 : ℝ) ≤ (10000747982982637/10000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (50015056321901276127/50000000000000000000 : ℝ)^512 ≤ (10000747982982637/10000000000000000 : ℝ)^2061 := by
      have hnat : (50015056321901276127 : ℕ)^512*10000000000000000^2061 ≤ 10000747982982637^2061*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015056321901276127 50000000000000000000 10000747982982637 10000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000747982982637/10000000000000000 : ℝ)) (X := (50015056321901276127/50000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025769319279105189/50000000000000000000 : ℝ) ≤ (5000640045458327/5000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (50025769319279105189/50000000000000000000 : ℝ)^512 ≤ (5000640045458327/5000000000000000 : ℝ)^2061 := by
      have hnat : (50025769319279105189 : ℕ)^512*5000000000000000^2061 ≤ 5000640045458327^2061*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025769319279105189 50000000000000000000 5000640045458327 5000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000640045458327/5000000000000000 : ℝ)) (X := (50025769319279105189/50000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036482316656934251/50000000000000000000 : ℝ) ≤ (10001812198850671/10000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (50036482316656934251/50000000000000000000 : ℝ)^512 ≤ (10001812198850671/10000000000000000 : ℝ)^2061 := by
      have hnat : (50036482316656934251 : ℕ)^512*10000000000000000^2061 ≤ 10001812198850671^2061*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036482316656934251 50000000000000000000 10001812198850671 10000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001812198850671/10000000000000000 : ℝ)) (X := (50036482316656934251/50000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15056321901276127/100000000000000000000 : ℝ) ≤ ((13805056328184142753/13810000000000000000 : ℝ)+2*(532107934017/276200000000000 : ℝ)*(351/3125 : ℝ))^(2061/512 : ℝ) := by
    rw [show (13805056328184142753/13810000000000000000 : ℝ)+2*(532107934017/276200000000000 : ℝ)*(351/3125 : ℝ)=(10000747982982637/10000000000000000 : ℝ) by norm_num, show 1+2*(15056321901276127/100000000000000000000 : ℝ)=(50015056321901276127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36482316656934251/100000000000000000000 : ℝ)+(15056321901276127/100000000000000000000 : ℝ) ≤ ((13805056328184142753/13810000000000000000 : ℝ)+(532107934017/276200000000000 : ℝ)*((6997/50000 : ℝ)+(351/3125 : ℝ)))^(2061/512 : ℝ) := by
    rw [show (13805056328184142753/13810000000000000000 : ℝ)+(532107934017/276200000000000 : ℝ)*((6997/50000 : ℝ)+(351/3125 : ℝ))=(5000640045458327/5000000000000000 : ℝ) by norm_num, show 1+(36482316656934251/100000000000000000000 : ℝ)+(15056321901276127/100000000000000000000 : ℝ)=(50025769319279105189/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36482316656934251/100000000000000000000 : ℝ) ≤ ((13805056328184142753/13810000000000000000 : ℝ)+2*(532107934017/276200000000000 : ℝ)*(6997/50000 : ℝ))^(2061/512 : ℝ) := by
    rw [show (13805056328184142753/13810000000000000000 : ℝ)+2*(532107934017/276200000000000 : ℝ)*(6997/50000 : ℝ)=(10001812198850671/10000000000000000 : ℝ) by norm_num, show 1+2*(36482316656934251/100000000000000000000 : ℝ)=(50036482316656934251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13805056328184142753/13810000000000000000 : ℝ)*(X 1 0+X 2 0)+(532107934017/276200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (13805056328184142753/13810000000000000000 : ℝ)) (alpha := (532107934017/276200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13805056328184142753/13810000000000000000 : ℝ)*(X 0 1+X 2 1)+(532107934017/276200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (13805056328184142753/13810000000000000000 : ℝ)) (alpha := (532107934017/276200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13805056328184142753/13810000000000000000 : ℝ)*(X 0 2+X 1 2)+(532107934017/276200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (13805056328184142753/13810000000000000000 : ℝ)) (alpha := (532107934017/276200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416145487/2000000000 : ℝ)*X 0 0+(67219487/125000000 : ℝ)*X 0 1+(5377558851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295040709/10000000000 : ℝ)*X 1 0+(-1096198459/5000000000 : ℝ)*X 1 1+(1075511787/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529504069/1000000000 : ℝ)*X 2 0+(1344389721/2500000000 : ℝ)*X 2 1+(-219239701/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4486065197/10000000000 : ℝ)*X 0 0+(4325406281/10000000000 : ℝ)*X 0 1+(2162703089/5000000000 : ℝ)*X 0 2+(4486065197/10000000000 : ℝ)*X 1 0+(4325406281/10000000000 : ℝ)*X 1 1+(2162703089/5000000000 : ℝ)*X 1 2+(4486065197/10000000000 : ℝ)*X 2 0+(4325406281/10000000000 : ℝ)*X 2 1+(2162703089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2342025273/10000000000 : ℝ)*X 0 0+(1319968931/2500000000 : ℝ)*X 0 1+(5279875579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((33526219/62500000 : ℝ)*X 1 0+(-2230542819/10000000000 : ℝ)*X 1 1+(5279875809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1341048937/2500000000 : ℝ)*X 2 0+(2639937641/5000000000 : ℝ)*X 2 1+(-2230542573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2134316907/5000000000 : ℝ)*X 0 0+(4434100139/10000000000 : ℝ)*X 0 1+(2217050273/5000000000 : ℝ)*X 0 2+(2134316907/5000000000 : ℝ)*X 1 0+(4434100139/10000000000 : ℝ)*X 1 1+(2217050273/5000000000 : ℝ)*X 1 2+(2134316907/5000000000 : ℝ)*X 2 0+(4434100139/10000000000 : ℝ)*X 2 1+(2217050273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-142968413/625000000 : ℝ)*X 0 0+(1042723903/2000000000 : ℝ)*X 0 1+(5387158253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322060259/2500000000 : ℝ)*X 1 0+(-2188577537/10000000000 : ℝ)*X 1 1+(1346789547/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322060277/2500000000 : ℝ)*X 2 0+(5387158207/10000000000 : ℝ)*X 2 1+(-1094288707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((180286351/400000000 : ℝ)*X 0 0+(4314718849/10000000000 : ℝ)*X 0 1+(2157359479/5000000000 : ℝ)*X 0 2+(180286351/400000000 : ℝ)*X 1 0+(4314718849/10000000000 : ℝ)*X 1 1+(2157359479/5000000000 : ℝ)*X 1 2+(180286351/400000000 : ℝ)*X 2 0+(4314718849/10000000000 : ℝ)*X 2 1+(2157359479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2135635907/10000000000 : ℝ)*X 0 0+(1360617161/2500000000 : ℝ)*X 0 1+(5271881689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369851719/10000000000 : ℝ)*X 1 0+(-2233605517/10000000000 : ℝ)*X 1 1+(263594109/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684925767/5000000000 : ℝ)*X 2 0+(5271882191/10000000000 : ℝ)*X 2 1+(-2233605749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4250609829/10000000000 : ℝ)*X 0 0+(177719637/400000000 : ℝ)*X 0 1+(4442990309/10000000000 : ℝ)*X 0 2+(4250609829/10000000000 : ℝ)*X 1 0+(177719637/400000000 : ℝ)*X 1 1+(4442990309/10000000000 : ℝ)*X 1 2+(4250609829/10000000000 : ℝ)*X 2 0+(177719637/400000000 : ℝ)*X 2 1+(4442990309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-214819538775378043195729146077607/345250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1172357/1250000000000 : ℝ)*(upper0) + (84209093/50000000000000 : ℝ)*(lower1) + (153011017/50000000000000 : ℝ)*(lower2) + (1922247328547791/50000000000000 : ℝ)*(major0) + (1922247328547791/50000000000000 : ℝ)*(major1) + (1922247328547791/50000000000000 : ℝ)*(major2) + (5374778213/100000000000000 : ℝ)*(sp1) + (3352458917/25000000000000 : ℝ)*(sp2) + (510718786855391/10000000000000 : ℝ)*(sp4) + (5107182638221521/100000000000000 : ℝ)*(sp5) + (2553587301582033/50000000000000 : ℝ)*(sp6) + (1301253660192667/50000000000000 : ℝ)*(sp7) + (144445823/100000000000000 : ℝ)*(sp8) + (3446246433/10000000000000 : ℝ)*(sp15) + (520508356569933/20000000000000 : ℝ)*(f.failure) + (2553594006499867/50000000000000 : ℝ)*(f.sum) + (26766751077487/6905000000000000000000000000 : ℝ)*base65 + (17554351928278658623/690500000000000000000000000000000 : ℝ)*base67 + (12843430812657658623/690500000000000000000000000000000 : ℝ)*base69 + (8854998643827658623/690500000000000000000000000000000 : ℝ)*base71 + (40874514273133/1726250000000000000000000000 : ℝ)*base73 + (18690047924740158623/690500000000000000000000000000000 : ℝ)*base75 + (7884022079722158623/690500000000000000000000000000000 : ℝ)*base77 + (26910506478149158623/690500000000000000000000000000000 : ℝ)*base79 + (57160888658867/6905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2335661/1000000000000000000000 : ℝ)*base90 + (2335661/1000000000000000000000 : ℝ)*base92 + (2335661/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (5923/10000 : ℝ) ≤ (25562645419719656000508732582501/43156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1429203/100000000000000 : ℝ)*(lower1) + (15494553/100000000000000 : ℝ)*(upper2) + (4303733/100000000000000 : ℝ)*(upper3) + (68595509/100000000000000 : ℝ)*(lower5) + (244199547430611/6250000000000 : ℝ)*(major0) + (244199547430611/6250000000000 : ℝ)*(major1) + (244199547430611/6250000000000 : ℝ)*(major2) + (514965581441831/10000000000000 : ℝ)*(sp0) + (160926624156249/3125000000000 : ℝ)*(sp1) + (1287413199687767/25000000000000 : ℝ)*(sp2) + (2644982733138719/100000000000000 : ℝ)*(sp3) + (1920709171/50000000000000 : ℝ)*(sp5) + (1507833621/50000000000000 : ℝ)*(sp6) + (2711148631/100000000000000 : ℝ)*(sp7) + (52899708885747/2000000000000 : ℝ)*(f.failure) + (514965581441831/10000000000000 : ℝ)*(f.sum) + (1453560073339/6905000000000000000000000000 : ℝ)*base66 + (926261992531112083/86312500000000000000000000000000 : ℝ)*base67 + (393439644192012917/86312500000000000000000000000000 : ℝ)*base70 + (76549510712700417/86312500000000000000000000000000 : ℝ)*base72 + (12284889415283/3452500000000000000000000000 : ℝ)*base73 + (1635694646483737083/86312500000000000000000000000000 : ℝ)*base75 + (180392190183299583/86312500000000000000000000000000 : ℝ)*base77 + (108689039653862083/86312500000000000000000000000000 : ℝ)*base79 + (95129390673243/3452500000000000000000000000 : ℝ)*base81 + (661101/100000000000000000000 : ℝ)*base89 + (661101/100000000000000000000 : ℝ)*base91 + (661101/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (9941/12500 : ℝ) ≤ (137289441085145346327481853795793/172625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33805701/100000000000000 : ℝ)*(upper0) + (29193769/50000000000000 : ℝ)*(lower3) + (61014991/100000000000000 : ℝ)*(upper4) + (2187720821684227/50000000000000 : ℝ)*(major0) + (2187720821684227/50000000000000 : ℝ)*(major1) + (2187720821684227/50000000000000 : ℝ)*(major2) + (29776696717/100000000000000 : ℝ)*(sp1) + (29246542693/50000000000000 : ℝ)*(sp2) + (245973007/800000000000 : ℝ)*(sp3) + (713209461/100000000000000 : ℝ)*(sp4) + (115248090831771/2000000000000 : ℝ)*(sp8) + (1152475095620259/20000000000000 : ℝ)*(sp9) + (46098774093701/800000000000 : ℝ)*(sp10) + (592387426994143/20000000000000 : ℝ)*(sp11) + (296196788159659/10000000000000 : ℝ)*(f.failure) + (5762405254798011/100000000000000 : ℝ)*(f.sum) + (3261955513919/1726250000000000000000000000 : ℝ)*base66 + (10723010396372593069/690500000000000000000000000000000 : ℝ)*base68 + (1851532596344906931/690500000000000000000000000000000 : ℝ)*base69 + (11057650552457093069/690500000000000000000000000000000 : ℝ)*base72 + (124245399029657/3452500000000000000000000000 : ℝ)*base73 + (9633356272888093069/690500000000000000000000000000000 : ℝ)*base76 + (6138908926120593069/690500000000000000000000000000000 : ℝ)*base78 + (16632001837315093069/690500000000000000000000000000000 : ℝ)*base80 + (13349835075309/6905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (8889397/500000000000000000000 : ℝ)*base89 + (8889397/500000000000000000000 : ℝ)*base91 + (8889397/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82921/100000 : ℝ) ≤ (-143137258885872837180686375587851/172625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82790473/100000000000000 : ℝ)*(lower0) + (261552493/100000000000000 : ℝ)*(upper3) + (63278003/100000000000000 : ℝ)*(lower4) + (2204945039594289/50000000000000 : ℝ)*(major0) + (2204945039594289/50000000000000 : ℝ)*(major1) + (2204945039594289/50000000000000 : ℝ)*(major2) + (2468156251/50000000000000 : ℝ)*(sp0) + (7985503951/10000000000000 : ℝ)*(sp5) + (1839020649/2000000000000 : ℝ)*(sp7) + (3291716627/100000000000000 : ℝ)*(sp8) + (234484937025083/4000000000000 : ℝ)*(sp12) + (2931025899308347/50000000000000 : ℝ)*(sp13) + (1465532913414051/25000000000000 : ℝ)*(sp14) + (1492597949437623/50000000000000 : ℝ)*(sp15) + (186580490619231/6250000000000 : ℝ)*(f.failure) + (1465532913414051/25000000000000 : ℝ)*(f.sum) + (26213499223951/3452500000000000000000000000 : ℝ)*base66 + (5698381212962687617/690500000000000000000000000000000 : ℝ)*base67 + (2306021146465812383/690500000000000000000000000000000 : ℝ)*base70 + (464666449715187617/690500000000000000000000000000000 : ℝ)*base71 + (18621761761947/6905000000000000000000000000 : ℝ)*base74 + (2396443357653187617/690500000000000000000000000000000 : ℝ)*base75 + (1076456665440187617/690500000000000000000000000000000 : ℝ)*base77 + (4792422537633187617/690500000000000000000000000000000 : ℝ)*base79 + (2662083835123/6905000000000000000000000000 : ℝ)*base81 + (2575473/312500000000000000000 : ℝ)*base89 + (2575473/312500000000000000000 : ℝ)*base91 + (2575473/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1052_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(5923/10000 : ℝ) else (9941/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82921/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1052_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1052_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(5923/10000 : ℝ) else (9941/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82921/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1052_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(5923/10000 : ℝ) else (9941/12500 : ℝ) ≤ X j i ∧ X j i ≤ (82921/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1052_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
